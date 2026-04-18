//! §6.2 defeasible rule:
//!
//! ```text
//!   [[Defeasible { base, exceptions }]] =
//!     let sorted = exceptions ordered by (priority DESC, source-position ASC) in
//!     choose {
//!       when [[g_1]] -> [[b_1]];
//!       ...;
//!       when [[g_n]] -> [[b_n]];
//!       else -> [[base]]
//!     }
//! ```
//!
//! The choose-arms encode defeasibility: a higher-priority exception, when
//! its guard holds, dominates all lower-priority arms and the base. When no
//! guard fires, the `else` falls through to the base body. Admissibility
//! requires the exceptions to totally order under (priority, source-position);
//! the ordering here realizes that requirement.
//!
//! The Op AST does not expose `choose` as an expression; it exposes
//! `Statement::Choose` with nested statement blocks. A rule body that
//! evaluates to a value therefore compiles into a nested chain of Op
//! expressions whose evaluation order matches the guard sequence. The
//! `OpExpr::Match` node, combined with boolean scrutinees, gives the same
//! computational content as a `choose` over the guard sequence.

use crate::ast::{LexException, LexTerm};
use crate::case_match::fail_closed_expr;
use crate::context::CompileCtx;
use crate::error::CompileError;
use op_core::{MatchArm, OpExpr};

/// Compile a defeasible rule.
///
/// Strategy: fold the sorted exception list into a nested `Match` over the
/// first guard. Each layer tests one guard; the `true` arm runs the
/// exception body, the `false` arm recurses into the next layer. The
/// innermost arm is the base body.
pub fn compile_defeasible(
    base: &LexTerm,
    exceptions: &[LexException],
    compile_one: &mut dyn FnMut(&LexTerm, &CompileCtx) -> Result<OpExpr, CompileError>,
    ctx: &CompileCtx,
) -> Result<OpExpr, CompileError> {
    // Sort exceptions: priority DESC, source-position ASC.
    let mut sorted: Vec<&LexException> = exceptions.iter().collect();
    sorted.sort_by(|a, b| {
        b.priority
            .cmp(&a.priority)
            .then(a.source_position.cmp(&b.source_position))
    });

    let compiled_base = compile_one(base, ctx)?;
    let mut acc = compiled_base;

    for exc in sorted.iter().rev() {
        let guard = compile_one(&exc.guard, ctx)?;
        let body = compile_one(&exc.body, ctx)?;
        acc = OpExpr::Match {
            scrutinee: Box::new(guard),
            arms: vec![
                MatchArm {
                    pattern: "true".to_string(),
                    binding: "_".to_string(),
                    body,
                },
                MatchArm {
                    pattern: "false".to_string(),
                    binding: "_".to_string(),
                    body: acc,
                },
            ],
            // Every boolean scrutinee is total on {true, false}; the
            // catch-all is a defence-in-depth fail-closed verdict.
            catch_all: Box::new(fail_closed_expr()),
        };
    }

    Ok(acc)
}
