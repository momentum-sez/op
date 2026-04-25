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
use op_core::OpType;
use std::collections::BTreeSet;

/// Run the admissibility predicate over a term. Returns `Ok(())` when the
/// term is admissible, otherwise returns a specific clause violation.
pub fn check_admissible(term: &LexTerm, prelude: &PreludeBinding) -> Result<(), CompileError> {
    check_admissible_with_binders(term, prelude, &BTreeSet::new())
}

fn check_admissible_with_binders(
    term: &LexTerm,
    prelude: &PreludeBinding,
    binders: &BTreeSet<String>,
) -> Result<(), CompileError> {
    match term {
        LexTerm::Const(v) => check_value_first_order(v),

        LexTerm::Var { name, .. } => {
            if prelude.lookup_value(name).is_some() || binders.contains(name) {
                Ok(())
            } else {
                Err(CompileError::UnboundVariable { name: name.clone() })
            }
        }

        LexTerm::Match {
            scrutinee,
            branches,
        } => {
            check_admissible_with_binders(scrutinee, prelude, binders)?;
            for b in branches {
                let mut branch_binders = binders.clone();
                if !b.binder.is_empty() && b.binder != "_" {
                    branch_binders.insert(b.binder.clone());
                }
                check_admissible_with_binders(&b.body, prelude, &branch_binders)?;
            }
            check_match_exhaustiveness(scrutinee, branches, prelude)
        }

        LexTerm::Defeasible {
            base, exceptions, ..
        } => {
            check_admissible_with_binders(base, prelude, binders)?;
            // §6.2 defeasible rule requires `(priority DESC, source_position ASC)` to
            // be a total order on the exception set. Two exceptions sharing the same
            // `(priority, source_position)` leave resolution non-deterministic;
            // reject at the admissibility gate so the compilation function stays
            // a function.
            let mut keys: Vec<(u32, u32)> = exceptions
                .iter()
                .map(|e| (e.priority, e.source_position))
                .collect();
            keys.sort();
            for w in keys.windows(2) {
                if w[0] == w[1] {
                    return Err(CompileError::NotAdmissible {
                        reason: AdmissibilityViolation::DefeasibleOrderNotTotal {
                            priority: w[0].0,
                            source_position: w[0].1,
                        },
                    });
                }
            }
            for e in exceptions {
                check_admissible_with_binders(&e.guard, prelude, binders)?;
                check_admissible_with_binders(&e.body, prelude, binders)?;
            }
            Ok(())
        }

        LexTerm::SanctionsDominance { principal } => {
            check_admissible_with_binders(principal, prelude, binders)
        }

        LexTerm::HoleFill { value, .. } => check_admissible_with_binders(value, prelude, binders),

        LexTerm::PreludeCall { callee, args } => {
            for a in args {
                check_admissible_with_binders(a, prelude, binders)?;
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
        // A prelude call whose declared return type has a decidable
        // constructor set admits match — Bool and Variant returns qualify.
        // Paper §6.1: exhaustiveness is decided on the scrutinee's TYPE when
        // that type has a finite registered constructor set.
        LexTerm::PreludeCall { callee, .. } => {
            prelude.lookup_callable(callee).and_then(|c| match &c.ty {
                OpType::Variant(ctors) => Some(ctors.iter().map(|(n, _)| n.clone()).collect()),
                OpType::Bool => Some(vec!["true".to_string(), "false".to_string()]),
                _ => None,
            })
        }
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

    let required_lookup: std::collections::BTreeSet<_> = required.iter().cloned().collect();
    let mut have = std::collections::BTreeSet::new();
    for branch in branches {
        if !required_lookup.contains(&branch.tag) {
            return Err(CompileError::NotAdmissible {
                reason: AdmissibilityViolation::ExhaustivenessUndecidable {
                    loc: LexLoc::default(),
                    detail: format!(
                        "branch `{}` is not in the scrutinee constructor set",
                        branch.tag
                    ),
                },
            });
        }
        if !have.insert(branch.tag.clone()) {
            return Err(CompileError::NotAdmissible {
                reason: AdmissibilityViolation::ExhaustivenessUndecidable {
                    loc: LexLoc::default(),
                    detail: format!("duplicate branch for `{}`", branch.tag),
                },
            });
        }
    }
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
