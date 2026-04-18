//! Effect rows and effect-safety analysis.
//!
//! Op effects compose by union. Some effect pairs impose ordering constraints
//! that the compiler enforces — in particular, any reachable `sovereign_write`,
//! `identity_mutation`, or `fiscal_transfer` must be dominated by a
//! `sanctions_check`, with a single deferred-subject exception: entity
//! creation where the subject does not yet exist.

use crate::ast::{Effect, OpExpr, OpProgram, Statement, StepBody};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use thiserror::Error;

/// An effect row is a set of effects.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EffectRow {
    set: BTreeSet<Effect>,
}

impl EffectRow {
    /// Empty effect row (pure).
    pub fn empty() -> Self {
        Self::default()
    }

    /// Singleton effect row.
    pub fn singleton(e: Effect) -> Self {
        let mut set = BTreeSet::new();
        set.insert(e);
        Self { set }
    }

    /// Insert one effect.
    pub fn insert(&mut self, e: Effect) {
        if !matches!(e, Effect::Pure) {
            self.set.insert(e);
        }
    }

    /// Union of two effect rows.
    pub fn union(mut self, other: &EffectRow) -> EffectRow {
        for e in &other.set {
            self.set.insert(e.clone());
        }
        self
    }

    /// Check whether an effect is present.
    pub fn contains(&self, e: &Effect) -> bool {
        self.set.contains(e)
    }

    /// Iterate over the effects in canonical (sorted) order.
    pub fn iter(&self) -> impl Iterator<Item = &Effect> {
        self.set.iter()
    }

    /// Number of effects in the row.
    pub fn len(&self) -> usize {
        self.set.len()
    }

    /// Row is empty (pure).
    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }
}

impl From<Vec<Effect>> for EffectRow {
    fn from(v: Vec<Effect>) -> Self {
        let mut row = EffectRow::empty();
        for e in v {
            row.insert(e);
        }
        row
    }
}

/// Effect-safety error surfaced by the analyzer.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum EffectSafetyError {
    /// A write-class effect appeared without a dominating sanctions check.
    #[error(
        "{effect:?} at step '{step}' is not dominated by a sanctions_check and does not qualify for \
         the deferred-subject exception"
    )]
    UndominatedWrite {
        /// The write-class effect.
        effect: Effect,
        /// The offending step identifier.
        step: String,
    },

    /// A step declared a compensation branch but no compensable effect.
    #[error("compensation branch on step '{step}' has no compensable effect")]
    CompensationWithoutCompensableEffect {
        /// Step identifier.
        step: String,
    },

    /// A `continue` failure action was declared on a sovereign-write step.
    /// This is the 'silently burying a failed mutation' class.
    #[error("step '{step}' would silently bury a sovereign mutation under a 'continue' failure")]
    ContinueOnSovereignWrite {
        /// Step identifier.
        step: String,
    },
}

/// The set of write-class effects that require a dominating sanctions check.
pub fn write_class_effects() -> BTreeSet<Effect> {
    let mut s = BTreeSet::new();
    s.insert(Effect::SovereignWrite);
    s.insert(Effect::IdentityMutation);
    s.insert(Effect::FiscalTransfer);
    s
}

/// Analyze a program's effect safety.
///
/// A simple dominator analysis walks the program body linearly (the ordering
/// of `Statement`s encodes the dependency edge from `depends_on`). A step is
/// dominated by a sanctions check when an earlier step in the same linear
/// prefix carries `Effect::SanctionsCheck`. Because real programs may use
/// `par` and `choose`, each branch is analyzed independently and the check
/// is satisfied if the dominator appears on every path.
pub fn check_effect_safety(program: &OpProgram) -> Result<(), Vec<EffectSafetyError>> {
    let mut ctx = SafetyCtx::default();
    ctx.walk_block(&program.body);
    if ctx.errors.is_empty() {
        Ok(())
    } else {
        Err(ctx.errors)
    }
}

#[derive(Default)]
struct SafetyCtx {
    sanctions_seen: bool,
    errors: Vec<EffectSafetyError>,
}

impl SafetyCtx {
    fn walk_block(&mut self, stmts: &[Statement]) {
        for stmt in stmts {
            self.walk_stmt(stmt);
        }
    }

    fn walk_stmt(&mut self, stmt: &Statement) {
        match stmt {
            Statement::Step(step) => {
                self.check_step(step);
                // Update sanctions visibility from this step's effects.
                if step.signature.effects.iter().any(|e| *e == Effect::SanctionsCheck) {
                    self.sanctions_seen = true;
                }
            }
            Statement::Let { .. } | Statement::Return(_) | Statement::Expr(_) | Statement::Run { .. } => {}
            Statement::Par { branches } => {
                // Each branch observes the current environment but cannot see siblings.
                let parent_sanctions = self.sanctions_seen;
                let mut all_sanctions_after = true;
                for (_name, _expr) in branches {
                    let sub = SafetyCtx {
                        sanctions_seen: parent_sanctions,
                        errors: Vec::new(),
                    };
                    // Flat expression branches do not introduce steps today.
                    // A future extension could walk nested step bodies here.
                    if !sub.sanctions_seen {
                        all_sanctions_after = false;
                    }
                    self.errors.extend(sub.errors);
                }
                self.sanctions_seen = parent_sanctions || all_sanctions_after;
            }
            Statement::Choose { arms, else_block } => {
                let parent = self.sanctions_seen;
                let mut every_branch_gates = true;
                for (_guard, branch) in arms {
                    let mut sub = SafetyCtx {
                        sanctions_seen: parent,
                        errors: Vec::new(),
                    };
                    sub.walk_block(branch);
                    if !sub.sanctions_seen {
                        every_branch_gates = false;
                    }
                    self.errors.extend(sub.errors);
                }
                if let Some(else_body) = else_block {
                    let mut sub = SafetyCtx {
                        sanctions_seen: parent,
                        errors: Vec::new(),
                    };
                    sub.walk_block(else_body);
                    if !sub.sanctions_seen {
                        every_branch_gates = false;
                    }
                    self.errors.extend(sub.errors);
                } else {
                    // Missing else-branch means the pre-choice path continues unchanged.
                    if !parent {
                        every_branch_gates = false;
                    }
                }
                self.sanctions_seen = parent || every_branch_gates;
            }
            Statement::In { body, .. } => {
                self.walk_block(body);
            }
            Statement::Policy { .. } => {}
        }
    }

    fn check_step(&mut self, step: &crate::ast::OpStep) {
        let write_class = write_class_effects();
        let step_has_write = step
            .signature
            .effects
            .iter()
            .any(|e| write_class.contains(e));

        if step_has_write && !self.sanctions_seen {
            // Deferred-subject exception: if the step is an entity-creation
            // primitive, the sanctions check is allowed to run post-flight.
            if !is_entity_create_primitive(&step.body) {
                for e in &step.signature.effects {
                    if write_class.contains(e) {
                        self.errors.push(EffectSafetyError::UndominatedWrite {
                            effect: e.clone(),
                            step: step.id.clone(),
                        });
                    }
                }
            }
        }

        // Compensation sanity: a compensation clause requires at least one
        // compensable effect (sovereign_write or fiscal_transfer).
        if step.compensate.is_some() {
            let has_compensable = step.signature.effects.iter().any(|e| {
                matches!(
                    e,
                    Effect::SovereignWrite | Effect::FiscalTransfer | Effect::IdentityMutation
                )
            });
            if !has_compensable {
                self.errors
                    .push(EffectSafetyError::CompensationWithoutCompensableEffect {
                        step: step.id.clone(),
                    });
            }
        }

        // Continue-on-sovereign-write is forbidden.
        if matches!(step.on_failure, Some(crate::ast::FailureAction::Continue))
            && step
                .signature
                .effects
                .iter()
                .any(|e| *e == Effect::SovereignWrite)
        {
            self.errors.push(EffectSafetyError::ContinueOnSovereignWrite {
                step: step.id.clone(),
            });
        }
    }
}

/// Identify the deferred-subject entity-creation primitive family.
/// The spec lists `create.entity` as the canonical case.
fn is_entity_create_primitive(body: &StepBody) -> bool {
    match body {
        StepBody::Primitive(p, _) => {
            let n = &p.0;
            n == "create.entity" || n.starts_with("entity.create")
        }
        StepBody::Block(_) => false,
    }
}

/// Flatten all effects occurring in any expression (used when computing
/// program-level effect rows from a mixed body).
#[allow(dead_code)]
pub(crate) fn expr_effects(expr: &OpExpr) -> EffectRow {
    match expr {
        OpExpr::Await { event, .. } => EffectRow::singleton(Effect::Await(event.clone())),
        OpExpr::ConsumeLinear(inner)
        | OpExpr::Lock { resource: inner, .. } => expr_effects(inner),
        OpExpr::CommitTransfer { locked, witness }
        | OpExpr::ReleaseLock {
            locked,
            witness,
        } => expr_effects(locked).union(&expr_effects(witness)),
        OpExpr::Record(fields) => fields.iter().fold(EffectRow::empty(), |acc, (_, e)| {
            acc.union(&expr_effects(e))
        }),
        OpExpr::List(items) | OpExpr::Tuple(items) => items
            .iter()
            .fold(EffectRow::empty(), |acc, e| acc.union(&expr_effects(e))),
        OpExpr::Call(_, args) => args.iter().fold(EffectRow::empty(), |acc, (_, e)| {
            acc.union(&expr_effects(e))
        }),
        OpExpr::BinOp(_, a, b) => expr_effects(a).union(&expr_effects(b)),
        OpExpr::UnOp(_, a) => expr_effects(a),
        OpExpr::Coalesce(a, b) => expr_effects(a).union(&expr_effects(b)),
        OpExpr::Seq(a, b) => expr_effects(a).union(&expr_effects(b)),
        OpExpr::Field(e, _) => expr_effects(e),
        OpExpr::Match { scrutinee, arms, catch_all } => {
            let mut row = expr_effects(scrutinee);
            for arm in arms {
                row = row.union(&expr_effects(&arm.body));
            }
            row.union(&expr_effects(catch_all))
        }
        _ => EffectRow::empty(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;

    fn step_with_effects(id: &str, effects: Vec<Effect>) -> OpStep {
        OpStep {
            id: id.to_string(),
            body: StepBody::Primitive(Primitive("some.op".to_string()), vec![]),
            signature: StepSignature {
                input: OpType::Unit,
                output: OpType::Unit,
                effects,
            },
            wait: None,
            on_failure: None,
            compensate: None,
            contracts: Contracts::default(),
        }
    }

    fn program(body: Vec<Statement>) -> OpProgram {
        OpProgram {
            name: "t.op".to_string(),
            jurisdiction: "_default".to_string(),
            metadata: ProgramMetadata::default(),
            inputs: vec![],
            outputs: vec![],
            effects: vec![],
            participants: vec![],
            approval: None,
            contracts: Contracts::default(),
            body,
            gas_budget: GasBudget::default(),
        }
    }

    #[test]
    fn effect_row_union_deduplicates() {
        let a = EffectRow::from(vec![Effect::SovereignWrite, Effect::Read]);
        let b = EffectRow::from(vec![Effect::Read, Effect::SanctionsCheck]);
        let c = a.union(&b);
        assert_eq!(c.len(), 3);
    }

    #[test]
    fn undominated_sovereign_write_is_rejected() {
        let prog = program(vec![Statement::Step(step_with_effects(
            "cap_table",
            vec![Effect::SovereignWrite],
        ))]);
        let err = check_effect_safety(&prog).unwrap_err();
        assert!(matches!(err[0], EffectSafetyError::UndominatedWrite { .. }));
    }

    #[test]
    fn sanctions_check_dominates_downstream_writes() {
        let prog = program(vec![
            Statement::Step(step_with_effects("gate", vec![Effect::SanctionsCheck])),
            Statement::Step(step_with_effects("write", vec![Effect::SovereignWrite])),
        ]);
        assert!(check_effect_safety(&prog).is_ok());
    }

    #[test]
    fn deferred_subject_entity_create_allowed() {
        let step = OpStep {
            id: "create".to_string(),
            body: StepBody::Primitive(Primitive("create.entity".to_string()), vec![]),
            signature: StepSignature {
                input: OpType::Unit,
                output: OpType::EntityRef,
                effects: vec![Effect::SovereignWrite],
            },
            wait: None,
            on_failure: None,
            compensate: None,
            contracts: Contracts::default(),
        };
        let prog = program(vec![Statement::Step(step)]);
        assert!(check_effect_safety(&prog).is_ok());
    }

    #[test]
    fn continue_on_sovereign_write_rejected() {
        let mut step = step_with_effects(
            "silent_write",
            vec![Effect::SanctionsCheck, Effect::SovereignWrite],
        );
        step.on_failure = Some(FailureAction::Continue);
        let prog = program(vec![Statement::Step(step)]);
        let err = check_effect_safety(&prog).unwrap_err();
        assert!(err
            .iter()
            .any(|e| matches!(e, EffectSafetyError::ContinueOnSovereignWrite { .. })));
    }

    #[test]
    fn compensation_without_compensable_effect_rejected() {
        let mut step = step_with_effects("doc", vec![Effect::DocumentGeneration]);
        step.compensate = Some(CompensationClause {
            body: StepBody::Primitive(Primitive("noop".to_string()), vec![]),
            invalidated_domains: vec![],
        });
        let prog = program(vec![Statement::Step(step)]);
        let err = check_effect_safety(&prog).unwrap_err();
        assert!(err
            .iter()
            .any(|e| matches!(e, EffectSafetyError::CompensationWithoutCompensableEffect { .. })));
    }

    #[test]
    fn choose_both_arms_gate_satisfies_dominator() {
        let prog = program(vec![
            Statement::Choose {
                arms: vec![(
                    OpExpr::Bool(true),
                    vec![Statement::Step(step_with_effects(
                        "gate_a",
                        vec![Effect::SanctionsCheck],
                    ))],
                )],
                else_block: Some(vec![Statement::Step(step_with_effects(
                    "gate_b",
                    vec![Effect::SanctionsCheck],
                ))]),
            },
            Statement::Step(step_with_effects(
                "write",
                vec![Effect::SovereignWrite],
            )),
        ]);
        assert!(check_effect_safety(&prog).is_ok());
    }
}
