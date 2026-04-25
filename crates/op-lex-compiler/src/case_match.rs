//! §6.2 match rule:
//!
//! ```text
//!   [[match e { | C_i x_i => b_i }]] =
//!       match [[e]] with
//!         | C_1 x_1 -> [[b_1]]
//!         | ...
//!         | C_n x_n -> [[b_n]]
//!         | _ -> fail-closed
//! ```
//!
//! The catch-all arm is materialized explicitly so the Op `Match` is total on
//! values. Admissibility has already decided the match is exhaustive — the
//! catch-all is a typed defence-in-depth inhabitant of the branch result type
//! against runtime-observed constructors not present in the compile-time type.
//! Verdict-valued matches use the canonical `NonCompliant` verdict tagged with
//! the reason `"pattern_unmatched"`.
//!
//! Each branch is compiled under a context extended with the branch's
//! constructor-payload binders. The admissible fragment's nullary
//! constructors carry a vacuous binder set, but the compiler still threads
//! the extension through so a later relaxation of admissibility (dependent
//! match) lands on a code path that already scopes binders correctly.

use crate::ast::LexBranch;
use crate::context::CompileCtx;
use crate::error::CompileError;
use op_core::{MatchArm, OpExpr, OpType};

/// Compile a match expression.
pub fn compile_match(
    scrutinee: OpExpr,
    branches: &[LexBranch],
    compile_one: &mut dyn FnMut(&crate::ast::LexTerm, &CompileCtx) -> Result<OpExpr, CompileError>,
    ctx: &CompileCtx,
) -> Result<OpExpr, CompileError> {
    let mut arms = Vec::with_capacity(branches.len());
    for b in branches {
        // Extend the context with this branch's binder bound to the payload
        // type. The admissible fragment restricts payloads to first-order
        // data, so `OpType::Record(vec![])` is a sound conservative choice
        // until the admissible fragment opens up dependent match.
        let branch_binders = binders_for_branch(b);
        let branch_ctx = ctx.with_binders(branch_binders);
        let body = compile_one(&b.body, &branch_ctx)?;
        arms.push(MatchArm {
            pattern: b.tag.clone(),
            binding: b.binder.clone(),
            body,
        });
    }
    let result_ty = arms
        .first()
        .map(|arm| crate::infer_expr_type(&arm.body, ctx))
        .unwrap_or(OpType::Unit);
    let catch_all = fail_closed_expr_for_type(&result_ty);
    Ok(OpExpr::Match {
        scrutinee: Box::new(scrutinee),
        arms,
        catch_all: Box::new(catch_all),
    })
}

/// Produce the binder list introduced by a single match branch.
///
/// The binder is the constructor's payload name; its type is the payload
/// type carried by the scrutinee's variant. Nullary constructors (the
/// admissible fragment today) use the bookkeeping binder `"_"` bound to
/// the unit type; non-trivial binders use `Record(vec![])` as a
/// conservative first-order placeholder.
fn binders_for_branch(b: &LexBranch) -> Vec<(String, OpType)> {
    if b.binder.is_empty() || b.binder == "_" {
        return Vec::new();
    }
    vec![(b.binder.clone(), OpType::Record(vec![]))]
}

/// The fail-closed verdict — a `Verdict::NonCompliant { reason }` record
/// compatible with the canonical prelude's `Verdict` variant.
pub fn fail_closed_expr() -> OpExpr {
    OpExpr::Record(vec![
        (
            "tag".to_string(),
            OpExpr::String("NonCompliant".to_string()),
        ),
        (
            "value".to_string(),
            OpExpr::Record(vec![(
                "reason".to_string(),
                OpExpr::String("pattern_unmatched".to_string()),
            )]),
        ),
    ])
}

/// Typed defense-in-depth catch-all for an already-exhaustive match.
///
/// The admissibility gate proves the catch-all unreachable for the registered
/// constructor set. The emitted Op still materializes a branch, so its value
/// must inhabit the same result type as the real arms.
pub fn fail_closed_expr_for_type(ty: &OpType) -> OpExpr {
    match ty {
        OpType::Unit => OpExpr::Unit,
        OpType::Bool => OpExpr::Bool(false),
        OpType::Int => OpExpr::Int(0),
        OpType::String => OpExpr::String("pattern_unmatched".to_string()),
        OpType::Record(fields) => OpExpr::Record(
            fields
                .iter()
                .map(|(name, field_ty)| (name.clone(), fail_closed_expr_for_type(field_ty)))
                .collect(),
        ),
        OpType::Variant(_) => fail_closed_expr(),
        OpType::List(_) => OpExpr::List(vec![]),
        OpType::Option(_) => OpExpr::Null,
        OpType::Tuple(items) => {
            OpExpr::Tuple(items.iter().map(fail_closed_expr_for_type).collect())
        }
        _ => OpExpr::Unit,
    }
}
