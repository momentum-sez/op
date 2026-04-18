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

use crate::ast::LexBranch;
use crate::context::CompileCtx;
use crate::error::CompileError;
use op_core::{MatchArm, OpExpr};

/// Compile a match expression.
pub fn compile_match(
    scrutinee: OpExpr,
    branches: &[LexBranch],
    compile_one: &mut dyn FnMut(&crate::ast::LexTerm, &CompileCtx) -> Result<OpExpr, CompileError>,
    ctx: &CompileCtx,
) -> Result<OpExpr, CompileError> {
    let mut arms = Vec::with_capacity(branches.len());
    for b in branches {
        let body = compile_one(&b.body, ctx)?;
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
