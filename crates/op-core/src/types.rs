//! Op type checker.
//!
//! The checker is bidirectional: `check(e, T)` synthesizes or checks against
//! `T`. It tracks linear-resource consumption, rejects double-use, confirms
//! effect rows compose with the program-level declaration, and discharges
//! declared safety predicates by passing them to the host at runtime.
//!
//! This implementation is deliberately compact. It covers the well-formed
//! shape of a program — bindings, types, steps, branches — and surfaces the
//! classes of errors that the spec requires at compile time: linearity,
//! undeclared variables, missing await-typing, and structural mismatches.
//! Rich semantic checks (e.g. cross-participant quorum validation) are the
//! host's responsibility.

use crate::ast::{
    Effect, OpExpr, OpProgram, OpType, SafetyPredicate, Statement, StepBody,
};
use crate::effects::check_effect_safety;
use crate::error::OpError;
use crate::gas::{estimate_structural_gas, StructuralCostTable};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeSet, HashMap, HashSet};

/// Type-checking context.
#[derive(Debug, Clone, Default)]
pub struct TypeContext {
    /// Variable type bindings.
    bindings: HashMap<String, OpType>,
    /// Linear resource names that have been consumed.
    pub(crate) consumed_linears: HashSet<String>,
    /// Locked resource names (currently in a locked state).
    pub(crate) locked: HashSet<String>,
    /// Obligations raised when `choose` / `par` branches consume a linear
    /// asymmetrically: if one arm consumed but another didn't, the
    /// non-consuming arm must not reference the name downstream. Keyed by
    /// resource name, carrying the source arm index for diagnostics.
    pub(crate) branch_asymmetric_consumptions: Vec<String>,
}

impl TypeContext {
    /// Fresh empty context.
    pub fn new() -> Self {
        Self::default()
    }

    /// Bind a variable to a type.
    pub fn bind(&mut self, name: String, ty: OpType) {
        self.bindings.insert(name, ty);
    }

    /// Look up a variable.
    pub fn lookup(&self, name: &str) -> Option<&OpType> {
        self.bindings.get(name)
    }

    /// Mark a linear resource as consumed.
    pub fn consume_linear(&mut self, name: &str) -> Result<(), OpError> {
        if self.consumed_linears.contains(name) {
            return Err(OpError::LinearityViolation(name.to_string()));
        }
        self.consumed_linears.insert(name.to_string());
        Ok(())
    }

    /// Check whether a linear resource has already been consumed.
    pub fn is_consumed(&self, name: &str) -> bool {
        self.consumed_linears.contains(name)
    }

    /// Mark a resource as locked.
    pub fn lock(&mut self, name: &str) {
        self.locked.insert(name.to_string());
    }

    /// Check whether a resource is locked.
    pub fn is_locked(&self, name: &str) -> bool {
        self.locked.contains(name)
    }

    /// Reconcile consumption state across independently-analyzed branches.
    ///
    /// Takes the union of consumed-linear sets: a name that was consumed
    /// along ANY branch is globally flagged as consumed after the branch
    /// point. When a name is consumed asymmetrically (some branches consumed
    /// it, others did not), that name is recorded as an asymmetric
    /// consumption so downstream references become type errors.
    pub(crate) fn reconcile_branches(&mut self, branches: &[TypeContext]) {
        if branches.is_empty() {
            return;
        }
        let mut union: HashSet<String> = HashSet::new();
        let mut intersection: Option<HashSet<String>> = None;
        for b in branches {
            union.extend(b.consumed_linears.iter().cloned());
            intersection = Some(match intersection.take() {
                None => b.consumed_linears.clone(),
                Some(prev) => prev.intersection(&b.consumed_linears).cloned().collect(),
            });
        }
        let all_consumed = intersection.unwrap_or_default();
        for name in &union {
            if !all_consumed.contains(name)
                && !self.branch_asymmetric_consumptions.contains(name)
            {
                self.branch_asymmetric_consumptions.push(name.clone());
            }
        }
        self.consumed_linears.extend(union);
        // Also carry forward any nested asymmetric obligations so nested
        // branches surface them at the top level.
        for b in branches {
            for n in &b.branch_asymmetric_consumptions {
                if !self.branch_asymmetric_consumptions.contains(n) {
                    self.branch_asymmetric_consumptions.push(n.clone());
                }
            }
        }
    }
}

/// Outcome of type-checking a program.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeCheckResult {
    /// Whether the program type-checks successfully.
    pub success: bool,
    /// Inferred program type (serialized as JSON-compatible string).
    pub inferred_type: Option<String>,
    /// Safety predicates that the program discharges statically.
    pub discharged_predicates: Vec<SafetyPredicate>,
    /// Safety predicates that the program requires but cannot discharge
    /// statically (host must discharge at run time).
    pub deferred_predicates: Vec<SafetyPredicate>,
    /// Safety predicates that failed to discharge and could not be deferred.
    pub failed_predicates: Vec<SafetyPredicateFailure>,
    /// Linearity violations.
    pub linearity_violations: Vec<String>,
    /// Gas analysis result.
    pub gas_analysis: Option<GasAnalysis>,
    /// Type errors.
    pub errors: Vec<String>,
}

/// A failed-to-discharge predicate with a diagnostic.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SafetyPredicateFailure {
    /// The predicate.
    pub predicate: SafetyPredicate,
    /// Why it failed.
    pub reason: String,
}

/// Gas analysis produced by the type checker.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GasAnalysis {
    /// Static structural gas bound.
    pub structural_bound: u64,
    /// Whether a runtime cardinality certificate is required.
    pub needs_cardinality_cert: bool,
    /// Extensional gas bound (if cardinality is known).
    pub max_extensional_gas: Option<u64>,
}

/// Type-check an Op program.
pub fn typecheck_program(program: &OpProgram) -> TypeCheckResult {
    let mut ctx = TypeContext::new();
    let mut errors: Vec<String> = Vec::new();
    let mut discharged: Vec<SafetyPredicate> = Vec::new();
    let mut deferred: Vec<SafetyPredicate> = Vec::new();

    // Seed context with inputs.
    for (name, ty) in &program.inputs {
        ctx.bind(name.clone(), ty.clone());
    }

    // Seed context with participants as EntityRef.
    for p in &program.participants {
        ctx.bind(p.name.clone(), OpType::EntityRef);
    }

    check_block(&program.body, &mut ctx, &mut errors, &mut discharged, &mut deferred);

    // Effect safety.
    if let Err(effect_errors) = check_effect_safety(program) {
        for e in effect_errors {
            errors.push(format!("{e}"));
        }
    }

    let gas_bound = estimate_structural_gas(&program.body, StructuralCostTable::default());
    let extensional_bound = program
        .gas_budget
        .cardinality_certificate
        .as_ref()
        .map(|c| program.gas_budget.per_element_gas.saturating_mul(c.cardinality));

    // Deterministic diagnostic order: a BTreeSet sorts names lexicographically
    // so replay runs emit the violations list in stable sequence. This backs
    // the replay-determinism claim in the op-core proof-bundle contract.
    let linearity_sorted: BTreeSet<String> = ctx
        .consumed_linears
        .iter()
        .filter(|n| ctx.locked.contains(n.as_str()))
        .cloned()
        .collect();
    TypeCheckResult {
        success: errors.is_empty(),
        inferred_type: Some(serde_json::to_string(&program.outputs).unwrap_or_default()),
        discharged_predicates: discharged,
        deferred_predicates: deferred,
        failed_predicates: vec![],
        linearity_violations: linearity_sorted.into_iter().collect(),
        gas_analysis: Some(GasAnalysis {
            structural_bound: gas_bound,
            needs_cardinality_cert: program.gas_budget.per_element_gas > 0
                && program.gas_budget.cardinality_certificate.is_none(),
            max_extensional_gas: extensional_bound,
        }),
        errors,
    }
}

fn check_block(
    stmts: &[Statement],
    ctx: &mut TypeContext,
    errors: &mut Vec<String>,
    discharged: &mut Vec<SafetyPredicate>,
    deferred: &mut Vec<SafetyPredicate>,
) {
    for stmt in stmts {
        check_statement(stmt, ctx, errors, discharged, deferred);
    }
}

fn check_statement(
    stmt: &Statement,
    ctx: &mut TypeContext,
    errors: &mut Vec<String>,
    discharged: &mut Vec<SafetyPredicate>,
    deferred: &mut Vec<SafetyPredicate>,
) {
    match stmt {
        Statement::Let { name, ty, value } => {
            if let Err(e) = check_expr(value, ctx) {
                errors.push(format!("in let {name}: {e}"));
            }
            ctx.bind(name.clone(), ty.clone());
        }
        Statement::Run { name, call } => {
            if let Err(e) = check_expr(call, ctx) {
                errors.push(format!("in run {name}: {e}"));
            }
            // The shape of a primitive call's return type is
            // host-determined; we bind to a record placeholder.
            ctx.bind(name.clone(), OpType::Record(vec![]));
        }
        Statement::Step(step) => {
            match &step.body {
                StepBody::Primitive(_, args) => {
                    for (_, arg) in args {
                        if let Err(e) = check_expr(arg, ctx) {
                            errors.push(format!("in step {}: {e}", step.id));
                        }
                    }
                }
                StepBody::Block(inner) => {
                    let mut inner_ctx = ctx.clone();
                    check_block(inner, &mut inner_ctx, errors, discharged, deferred);
                }
            }
            if let Some(comp) = &step.compensate {
                if let StepBody::Block(inner) = &comp.body {
                    let mut inner_ctx = ctx.clone();
                    check_block(inner, &mut inner_ctx, errors, discharged, deferred);
                }
                if let StepBody::Primitive(_, args) = &comp.body {
                    for (_, arg) in args {
                        if let Err(e) = check_expr(arg, ctx) {
                            errors.push(format!("in compensate of step {}: {e}", step.id));
                        }
                    }
                }
            }
            // Bind the step's output type so downstream statements can project.
            ctx.bind(step.id.clone(), step.signature.output.clone());
            // A suspending step binds an Await type.
            if let Some(w) = &step.wait {
                ctx.bind(
                    step.id.clone(),
                    OpType::Await {
                        event: w.event.clone(),
                        payload: Box::new(step.signature.output.clone()),
                    },
                );
            }
        }
        Statement::Par { branches } => {
            let mut branch_ctxs: Vec<TypeContext> = Vec::new();
            for (name, e) in branches {
                let mut sub = ctx.clone();
                if let Err(err) = check_expr(e, &mut sub) {
                    errors.push(format!("in par branch {name}: {err}"));
                }
                branch_ctxs.push(sub);
                ctx.bind(name.clone(), OpType::Record(vec![]));
            }
            ctx.reconcile_branches(&branch_ctxs);
        }
        Statement::Choose { arms, else_block } => {
            let mut branch_ctxs: Vec<TypeContext> = Vec::new();
            for (guard, block) in arms {
                if let Err(e) = check_expr(guard, ctx) {
                    errors.push(format!("in choose guard: {e}"));
                }
                let mut sub = ctx.clone();
                check_block(block, &mut sub, errors, discharged, deferred);
                branch_ctxs.push(sub);
            }
            if let Some(else_body) = else_block {
                let mut sub = ctx.clone();
                check_block(else_body, &mut sub, errors, discharged, deferred);
                branch_ctxs.push(sub);
            }
            ctx.reconcile_branches(&branch_ctxs);
        }
        Statement::In { body, .. } => {
            check_block(body, ctx, errors, discharged, deferred);
        }
        Statement::Policy { .. } => {
            // Policy blocks defer to host-side SAVM / proof backend.
        }
        Statement::Return(e) | Statement::Expr(e) => {
            if let Err(err) = check_expr(e, ctx) {
                errors.push(err);
            }
            if let OpExpr::AssertSafety(pred) = e {
                discharged.push(pred.clone());
            }
        }
    }
}

fn check_expr(expr: &OpExpr, ctx: &mut TypeContext) -> Result<(), String> {
    match expr {
        OpExpr::Unit
        | OpExpr::Bool(_)
        | OpExpr::Int(_)
        | OpExpr::String(_)
        | OpExpr::Null => Ok(()),
        OpExpr::Var(name) => {
            if ctx.lookup(name).is_some() {
                if ctx.consumed_linears.contains(name) {
                    return Err(format!(
                        "linear-use-after-consume: {name} was consumed earlier in this branch"
                    ));
                }
                Ok(())
            } else {
                Err(format!("unbound variable: {name}"))
            }
        }
        OpExpr::Field(base, _field) => check_expr(base, ctx),
        OpExpr::Record(fields) => {
            for (_name, e) in fields {
                check_expr(e, ctx)?;
            }
            Ok(())
        }
        OpExpr::List(items) | OpExpr::Tuple(items) => {
            for item in items {
                check_expr(item, ctx)?;
            }
            Ok(())
        }
        OpExpr::Call(_name, args) => {
            for (_, e) in args {
                check_expr(e, ctx)?;
            }
            Ok(())
        }
        OpExpr::BinOp(_, a, b) | OpExpr::Coalesce(a, b) => {
            check_expr(a, ctx)?;
            check_expr(b, ctx)
        }
        OpExpr::Seq(a, b) => {
            // Seq evaluates `a` for its effect, returns `b`'s value.
            // Type of a Seq expression is the type of its second operand.
            check_expr(a, ctx)?;
            check_expr(b, ctx)
        }
        OpExpr::UnOp(_, a) => check_expr(a, ctx),
        OpExpr::Await { .. } => Ok(()),
        OpExpr::Match {
            scrutinee,
            arms,
            catch_all,
        } => {
            check_expr(scrutinee, ctx)?;
            for arm in arms {
                let mut sub = ctx.clone();
                sub.bind(arm.binding.clone(), OpType::Unit);
                check_expr(&arm.body, &mut sub)?;
            }
            check_expr(catch_all, ctx)
        }
        OpExpr::AssertSafety(_) => Ok(()),
        OpExpr::ConsumeLinear(inner) => {
            if let OpExpr::Var(n) = inner.as_ref() {
                // The Var referenced here IS the consumption site, not a
                // post-consume use. Look up existence, then mark consumed.
                if ctx.lookup(n).is_none() {
                    return Err(format!("unbound variable: {n}"));
                }
                ctx.consume_linear(n).map_err(|e| e.to_string())?;
                Ok(())
            } else {
                check_expr(inner, ctx)
            }
        }
        OpExpr::Lock { resource, .. } => {
            if let OpExpr::Var(n) = resource.as_ref() {
                if ctx.lookup(n).is_none() {
                    return Err(format!("unbound variable: {n}"));
                }
                if ctx.consumed_linears.contains(n) {
                    return Err(format!(
                        "linear-use-after-consume: {n} cannot be locked after consumption"
                    ));
                }
                ctx.lock(n);
                Ok(())
            } else {
                check_expr(resource, ctx)
            }
        }
        OpExpr::CommitTransfer { locked, witness } => {
            if let OpExpr::Var(n) = locked.as_ref() {
                if !ctx.is_locked(n) {
                    return Err(format!(
                        "commit_transfer requires a locked resource; '{n}' is not locked"
                    ));
                }
                // Committing consumes the linear resource underlying the lock,
                // AND eliminates the Locked<T> wrapper — see F4.
                ctx.consume_linear(n).map_err(|e| e.to_string())?;
                ctx.locked.remove(n);
            } else {
                check_expr(locked, ctx)?;
            }
            check_expr(witness, ctx)
        }
        OpExpr::ReleaseLock { locked, witness } => {
            if let OpExpr::Var(n) = locked.as_ref() {
                if !ctx.is_locked(n) {
                    return Err(format!(
                        "release_lock requires a locked resource; '{n}' is not locked"
                    ));
                }
                // Release restores Locked<T> to Linear<T>; the linear is *not*
                // consumed. See F4 — remove the locked-wrapper name.
                ctx.locked.remove(n);
            } else {
                check_expr(locked, ctx)?;
            }
            check_expr(witness, ctx)
        }
    }
}

/// Effect-row composition: compute the union of effects declared at each step.
pub fn program_effect_row(program: &OpProgram) -> Vec<Effect> {
    let mut seen: Vec<Effect> = Vec::new();
    walk_for_effects(&program.body, &mut seen);
    seen.sort();
    seen.dedup();
    seen
}

fn walk_for_effects(stmts: &[Statement], acc: &mut Vec<Effect>) {
    for s in stmts {
        match s {
            Statement::Step(step) => {
                for e in &step.signature.effects {
                    acc.push(e.clone());
                }
                if let StepBody::Block(inner) = &step.body {
                    walk_for_effects(inner, acc);
                }
            }
            Statement::Par { branches: _ } => {}
            Statement::Choose { arms, else_block } => {
                for (_g, b) in arms {
                    walk_for_effects(b, acc);
                }
                if let Some(e) = else_block {
                    walk_for_effects(e, acc);
                }
            }
            Statement::In { body, .. } => walk_for_effects(body, acc),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;

    fn trivial_program(body: Vec<Statement>) -> OpProgram {
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
    fn empty_program_typechecks() {
        let res = typecheck_program(&trivial_program(vec![]));
        assert!(res.success);
    }

    #[test]
    fn unbound_variable_is_rejected() {
        let res = typecheck_program(&trivial_program(vec![Statement::Return(OpExpr::Var(
            "missing".to_string(),
        ))]));
        assert!(!res.success);
    }

    #[test]
    fn let_binding_brings_into_scope() {
        let res = typecheck_program(&trivial_program(vec![
            Statement::Let {
                name: "x".to_string(),
                ty: OpType::Int,
                value: OpExpr::Int(7),
            },
            Statement::Return(OpExpr::Var("x".to_string())),
        ]));
        assert!(res.success);
    }

    #[test]
    fn assert_safety_is_recorded_as_discharged() {
        let res = typecheck_program(&trivial_program(vec![Statement::Return(
            OpExpr::AssertSafety(SafetyPredicate::NoGroupFormationBypass),
        )]));
        assert!(res.success);
        assert_eq!(res.discharged_predicates.len(), 1);
    }

    #[test]
    fn linearity_double_use_is_rejected() {
        // Simulate: bind a linear, consume it twice.
        let mut ctx = TypeContext::new();
        ctx.bind(
            "share".to_string(),
            OpType::Linear(Box::new(OpType::String)),
        );
        assert!(ctx.consume_linear("share").is_ok());
        assert!(ctx.consume_linear("share").is_err());
    }

    #[test]
    fn commit_transfer_requires_locked() {
        let mut ctx = TypeContext::new();
        ctx.bind(
            "share".to_string(),
            OpType::Linear(Box::new(OpType::String)),
        );
        let expr = OpExpr::CommitTransfer {
            locked: Box::new(OpExpr::Var("share".to_string())),
            witness: Box::new(OpExpr::Unit),
        };
        assert!(check_expr(&expr, &mut ctx).is_err());
    }

    #[test]
    fn lock_then_release_keeps_linear_unconsumed() {
        let mut ctx = TypeContext::new();
        ctx.bind(
            "share".to_string(),
            OpType::Linear(Box::new(OpType::String)),
        );
        let lock = OpExpr::Lock {
            resource: Box::new(OpExpr::Var("share".to_string())),
            corridor_id: "corr-a".to_string(),
        };
        assert!(check_expr(&lock, &mut ctx).is_ok());
        assert!(ctx.is_locked("share"));
        let release = OpExpr::ReleaseLock {
            locked: Box::new(OpExpr::Var("share".to_string())),
            witness: Box::new(OpExpr::Unit),
        };
        assert!(check_expr(&release, &mut ctx).is_ok());
        assert!(!ctx.is_locked("share"));
        assert!(!ctx.is_consumed("share"));
    }

    #[test]
    fn var_after_consume_is_rejected() {
        // A linear resource consumed once, then referenced again via `Var`
        // in the same branch, must surface as a linear-use-after-consume
        // error at the Var lookup — not silently pass.
        let mut ctx = TypeContext::new();
        ctx.bind(
            "share".to_string(),
            OpType::Linear(Box::new(OpType::String)),
        );
        // Consume once.
        let consume = OpExpr::ConsumeLinear(Box::new(OpExpr::Var("share".to_string())));
        assert!(check_expr(&consume, &mut ctx).is_ok());
        // Referencing again via Var must be rejected.
        let use_again = OpExpr::Var("share".to_string());
        let err = check_expr(&use_again, &mut ctx).unwrap_err();
        assert!(
            err.contains("linear-use-after-consume"),
            "expected linear-use-after-consume, got: {err}"
        );
    }

    #[test]
    fn choose_reconciliation_flags_asymmetric_consumption() {
        // One arm consumes `share`; the other doesn't. After the choose, the
        // name is both globally considered consumed AND recorded as an
        // asymmetric consumption obligation.
        let prog = trivial_program(vec![
            Statement::Let {
                name: "share".to_string(),
                ty: OpType::Linear(Box::new(OpType::String)),
                value: OpExpr::String("s".to_string()),
            },
            Statement::Choose {
                arms: vec![(
                    OpExpr::Bool(true),
                    vec![Statement::Return(OpExpr::ConsumeLinear(Box::new(
                        OpExpr::Var("share".to_string()),
                    )))],
                )],
                else_block: Some(vec![Statement::Return(OpExpr::Unit)]),
            },
        ]);
        let res = typecheck_program(&prog);
        assert!(
            res.success,
            "program should typecheck: {errors:?}",
            errors = res.errors
        );
        // Downstream Var reference must now be rejected.
        let mut downstream = OpProgram {
            name: "after.choose".to_string(),
            jurisdiction: "_default".to_string(),
            metadata: ProgramMetadata::default(),
            inputs: vec![],
            outputs: vec![],
            effects: vec![],
            participants: vec![],
            approval: None,
            contracts: Contracts::default(),
            body: vec![
                Statement::Let {
                    name: "share".to_string(),
                    ty: OpType::Linear(Box::new(OpType::String)),
                    value: OpExpr::String("s".to_string()),
                },
                Statement::Choose {
                    arms: vec![(
                        OpExpr::Bool(true),
                        vec![Statement::Return(OpExpr::ConsumeLinear(Box::new(
                            OpExpr::Var("share".to_string()),
                        )))],
                    )],
                    else_block: Some(vec![Statement::Return(OpExpr::Unit)]),
                },
                Statement::Return(OpExpr::Var("share".to_string())),
            ],
            gas_budget: GasBudget::default(),
        };
        let res2 = typecheck_program(&downstream);
        assert!(
            !res2.success,
            "downstream reference to asymmetrically-consumed linear should be rejected"
        );
        // Silence the unused `downstream` mut.
        downstream.body.clear();
    }

    #[test]
    fn program_effect_row_aggregates_steps() {
        let step = OpStep {
            id: "gate".to_string(),
            body: StepBody::Primitive(Primitive("screen".to_string()), vec![]),
            signature: StepSignature {
                input: OpType::Unit,
                output: OpType::Bool,
                effects: vec![Effect::SanctionsCheck, Effect::ExternalRead],
            },
            wait: None,
            on_failure: None,
            compensate: None,
            contracts: Contracts::default(),
        };
        let prog = trivial_program(vec![Statement::Step(step)]);
        let row = program_effect_row(&prog);
        assert!(row.contains(&Effect::SanctionsCheck));
        assert!(row.contains(&Effect::ExternalRead));
    }
}
