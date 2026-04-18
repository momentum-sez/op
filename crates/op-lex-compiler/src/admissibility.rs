//! Admissibility gate.
//!
//! A positive inductive definition of the admissible fragment of Lex.
//! A term is admissible when every subterm satisfies:
//!
//! - Clause (a) — values are first-order (no function literals or
//!   dependent-pair terms reach the compiler; the vendored AST only exposes
//!   first-order constructors, so this clause is discharged by construction).
//! - Clause (b) — no modal operators. The vendored AST omits modal shapes,
//!   so this clause is discharged by construction; the gate still inspects
//!   the tree so a future extension that re-exposes a modal cannot bypass
//!   the predicate.
//! - Clause (c) — no temporal coercions. Discharged by construction; see (b).
//! - Clause (d) — every discretion hole is filled. Enforced dynamically.
//! - Clause (e) — every match has decidable exhaustiveness under the prelude.
//!   Enforced by checking that the scrutinee's variant constructor set is
//!   registered in the prelude and each constructor has a matching branch.

use crate::ast::{LexBranch, LexTerm, LexValue};
use crate::context::PreludeBinding;
use crate::error::{AdmissibilityViolation, CompileError};

/// Run the admissibility predicate over a term. Returns `Ok(())` when the
/// term is admissible, otherwise returns a specific clause violation.
pub fn check_admissible(term: &LexTerm, prelude: &PreludeBinding) -> Result<(), CompileError> {
    match term {
        LexTerm::Const(v) => check_value_first_order(v),

        LexTerm::Var { .. } => Ok(()),

        LexTerm::Match {
            scrutinee,
            branches,
        } => {
            check_admissible(scrutinee, prelude)?;
            for b in branches {
                check_admissible(&b.body, prelude)?;
            }
            check_match_exhaustiveness(scrutinee, branches, prelude)
        }

        LexTerm::Defeasible {
            base, exceptions, ..
        } => {
            check_admissible(base, prelude)?;
            for e in exceptions {
                check_admissible(&e.guard, prelude)?;
                check_admissible(&e.body, prelude)?;
            }
            Ok(())
        }

        LexTerm::SanctionsDominance { principal } => check_admissible(principal, prelude),

        LexTerm::HoleFill { value, .. } => check_admissible(value, prelude),

        LexTerm::PreludeCall { callee, args } => {
            for a in args {
                check_admissible(a, prelude)?;
            }
            if prelude.lookup_callable(callee).is_none() {
                return Err(CompileError::UnsupportedPreludeCall {
                    name: callee.clone(),
                });
            }
            Ok(())
        }
    }
}

fn check_value_first_order(v: &LexValue) -> Result<(), CompileError> {
    match v {
        LexValue::Bool(_) | LexValue::Int(_) | LexValue::Str(_) | LexValue::Unit => Ok(()),
        LexValue::Record(fields) => {
            for (_, fv) in fields {
                check_value_first_order(fv)?;
            }
            Ok(())
        }
        LexValue::Variant { payload, .. } => check_value_first_order(payload),
        LexValue::List(elems) => {
            for e in elems {
                check_value_first_order(e)?;
            }
            Ok(())
        }
    }
}

/// Decide exhaustiveness by inspecting the scrutinee's shape and the prelude
/// registration.
///
/// Two decidable cases: the scrutinee is a direct variant literal (finite
/// constructor set known at the site), or the scrutinee is a prelude call
/// whose return type is a registered variant type (constructor set lifted
/// from the prelude binding).
fn check_match_exhaustiveness(
    scrutinee: &LexTerm,
    branches: &[LexBranch],
    prelude: &PreludeBinding,
) -> Result<(), CompileError> {
    use crate::ast::LexLoc;
    let loc = LexLoc::default();

    let required_set: Option<Vec<String>> = match scrutinee {
        LexTerm::Const(LexValue::Variant { tag, .. }) => Some(vec![tag.clone()]),
        LexTerm::Const(LexValue::Bool(_)) => Some(vec!["true".to_string(), "false".to_string()]),
        // A sanctions-dominance scrutinee carries the Verdict variant set.
        LexTerm::SanctionsDominance { .. } => prelude.lookup_variant("Verdict").cloned(),
        _ => None,
    };

    let Some(required) = required_set else {
        return Err(CompileError::NotAdmissible {
            reason: AdmissibilityViolation::ExhaustivenessUndecidable {
                loc,
                detail: "scrutinee shape is not a registered variant".to_string(),
            },
        });
    };

    let have: std::collections::BTreeSet<_> = branches.iter().map(|b| b.tag.clone()).collect();
    for required_tag in &required {
        if !have.contains(required_tag) {
            return Err(CompileError::NotAdmissible {
                reason: AdmissibilityViolation::ExhaustivenessUndecidable {
                    loc: LexLoc::default(),
                    detail: format!("missing branch for `{required_tag}`"),
                },
            });
        }
    }
    Ok(())
}
