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
//! values. Fail-closed in this context means: return a `NonCompliant` verdict
//! tagged with the reason `"pattern_unmatched"`. Admissibility has already
//! decided the match is exhaustive — the catch-all is purely defence-in-depth
//! against runtime-observed constructors not present in the compile-time type.
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
    let catch_all = fail_closed_expr();
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
        ("tag".to_string(), OpExpr::String("NonCompliant".to_string())),
        (
            "value".to_string(),
            OpExpr::Record(vec![(
                "reason".to_string(),
                OpExpr::String("pattern_unmatched".to_string()),
            )]),
        ),
    ])
}
