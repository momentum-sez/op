//! Op type checker.
//!
//! The checker is bidirectional: `check(e, T)` synthesizes or checks against
//! `T`. It tracks linear-resource consumption, rejects double-use, confirms
//! effect rows compose with the program-level declaration, and rejects bare
//! safety predicates that carry no verified receipt.
//!
//! This implementation is deliberately compact. It covers the well-formed
//! shape of a program — bindings, types, steps, branches — and surfaces the
//! classes of errors that the spec requires at compile time: linearity,
//! undeclared variables, missing await-typing, and structural mismatches.
//! Rich semantic checks (e.g. cross-participant quorum validation) are the
//! host's responsibility.

use crate::ast::{
    BinOp, Effect, MatchArm, OpExpr, OpProgram, OpType, SafetyPredicate, Statement, StepBody, UnOp,
};
use crate::effects::{canonical_effects_for, check_effect_safety, expr_effects};
use crate::error::OpError;
use crate::gas::{estimate_structural_gas, StructuralCostTable};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// Type-checking context.
#[derive(Debug, Clone, Default)]
pub struct TypeContext {
    /// Variable type bindings.
    bindings: HashMap<String, OpType>,
    /// Linear resource names that have been consumed.
    pub(crate) consumed_linears: HashSet<String>,
    /// Locked resource names (currently in a locked state).
    pub(crate) locked: HashSet<String>,
    /// Resource names whose lock capability has been spent (commit-transfer or
    /// release-lock). The lock capability of an affine `Locked<T>` is
    /// single-use: once a lock has been committed or released, the same name
    /// may never be re-locked. This is what makes the lock/commit/release
    /// triple an *affine* discipline rather than an unbounded re-entrant one.
    /// A released name remains consumable as a `Linear<T>` (release restores
    /// the linear), but it can never be locked again. See F6.
    pub(crate) lock_spent: HashSet<String>,
    /// Real linearity/affinity violations observed during the walk, recorded
    /// by resource name. A violation is recorded whenever a linear resource is
    /// used after consumption, locked after consumption, accessed while
    /// locked, double-locked after its lock capability was spent, or
    /// double-consumed. These are surfaced in `TypeCheckResult.linearity_violations`.
    /// (Previously `linearity_violations` was computed as the intersection of
    /// `consumed_linears` and `locked`, which is structurally always empty —
    /// a name is removed from `locked` the instant it is consumed/released, so
    /// no violation was ever reported. See F1.)
    pub(crate) linearity_violations: BTreeSet<String>,
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
            // Record the real violation so it surfaces in
            // `linearity_violations`, then fail loud. See F1.
            self.linearity_violations.insert(name.to_string());
            return Err(OpError::LinearityViolation(name.to_string()));
        }
        self.consumed_linears.insert(name.to_string());
        Ok(())
    }

    /// Record a real linearity/affinity violation by resource name. Idempotent.
    pub(crate) fn record_linearity_violation(&mut self, name: &str) {
        self.linearity_violations.insert(name.to_string());
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
            if !all_consumed.contains(name) && !self.branch_asymmetric_consumptions.contains(name) {
                self.branch_asymmetric_consumptions.push(name.clone());
            }
        }
        self.consumed_linears.extend(union);
        // Carry forward lock-capability-spent and real linearity violations
        // from every branch: a lock spent or a violation observed on ANY arm
        // is globally true after the branch point (a name re-locked in arm A
        // must not be re-lockable downstream of the join; a violation seen in
        // arm B must be reported). See F1 / F6.
        for b in branches {
            self.lock_spent.extend(b.lock_spent.iter().cloned());
            self.linearity_violations
                .extend(b.linearity_violations.iter().cloned());
        }
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
    /// Asymmetric-consumption obligations: linear resource names consumed on
    /// some `choose`/`par` branch(es) but not all. A name listed here was made
    /// globally-consumed at the branch join, so any downstream reference is a
    /// linearity error; the obligation is surfaced so callers/regulators can
    /// see which resources carry an arm-asymmetric consumption. See F7.
    pub asymmetric_consumption_obligations: Vec<String>,
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

// FOLLOW-ON (deliberately NOT implemented in this soundness pass — these are
// FEATURES, not soundness bugs in the linear/affine core): two pack-binding
// checks specified in `docs/proposal-lex-rule-contract-and-pack-binding.md` §3
// remain open work for `typecheck_program`:
//   * `type-checker-no-contract-validation` — §3.1 completeness: query the
//     active pack for every Lex rule whose `applies_to` matches the program's
//     (operation_type, jurisdiction) and reject if the program's `requires`
//     omits any (`TypeError::IncompleteLexDischarge`).
//   * `structural-discharge-not-implemented` — §3.2 per-rule structural
//     discharge: a syntactic, decidable check that walks the program body and
//     verifies a structural witness exists for each declared rule's compiled
//     predicate (sanctions_check gating writes, governance_request on a policy,
//     obligation-before-write effect-DAG domination, certificate proof_emit).
// Both require a pack handle / `CompiledTerm` contract that `op-core` does not
// yet carry; they are joint `lex-core` + `op-stdlib` + `op-core` surface (see
// proposal §3.2). They do not affect the linear/affine soundness fixed here.

/// Type-check an Op program.
pub fn typecheck_program(program: &OpProgram) -> TypeCheckResult {
    let mut ctx = TypeContext::new();
    let mut errors: Vec<String> = Vec::new();
    let mut discharged: Vec<SafetyPredicate> = Vec::new();
    let mut deferred: Vec<SafetyPredicate> = Vec::new();
    let mut failed: Vec<SafetyPredicateFailure> = Vec::new();

    // Seed context with inputs.
    for (name, ty) in &program.inputs {
        ctx.bind(name.clone(), ty.clone());
    }

    // Seed context with participants as EntityRef.
    for p in &program.participants {
        ctx.bind(p.name.clone(), OpType::EntityRef);
    }

    let expected_output = program_output_type(&program.outputs);
    check_block(
        &program.body,
        &mut ctx,
        &mut errors,
        &mut discharged,
        &mut deferred,
        &mut failed,
        expected_output.as_ref(),
    );
    if let Some(expected) = &expected_output {
        if expected != &OpType::Unit && !block_contains_return(&program.body) {
            errors.push(format!(
                "program declares output {expected:?} but contains no return"
            ));
        }
    }

    // Effect safety.
    if let Err(effect_errors) = check_effect_safety(program) {
        for e in effect_errors {
            errors.push(format!("{e}"));
        }
    }

    let inferred_effects = program_effect_row(program);
    let declared_effects: BTreeSet<Effect> = program
        .effects
        .iter()
        .filter(|e| !matches!(e, Effect::Pure))
        .cloned()
        .collect();
    let missing_effects: Vec<Effect> = inferred_effects
        .iter()
        .filter(|e| !matches!(e, Effect::Pure) && !declared_effects.contains(*e))
        .cloned()
        .collect();
    if !missing_effects.is_empty() {
        errors.push(format!(
            "program effect declaration missing inferred effects: {missing_effects:?}"
        ));
    }

    let gas_bound = estimate_structural_gas(&program.body, StructuralCostTable::default());
    // Extensional bound = per_element_gas × cardinality. A `saturating_mul`
    // here silently caps at `u64::MAX`, which would mint a *valid-looking*
    // finite bound for an arithmetic overflow — a program whose true
    // extensional cost cannot be represented would type-check with a bogus
    // ceiling. Use `checked_mul` and reject on overflow (fail loud). See F10.
    let mut extensional_bound: Option<u64> = None;
    if let Some(c) = program.gas_budget.cardinality_certificate.as_ref() {
        match program.gas_budget.per_element_gas.checked_mul(c.cardinality) {
            Some(bound) => extensional_bound = Some(bound),
            None => errors.push(format!(
                "extensional gas bound overflows u64: per_element_gas {} × cardinality {} \
                 (query `{}`) is not representable",
                program.gas_budget.per_element_gas, c.cardinality, c.query
            )),
        }
    }

    // Surface the computed structural gas bound against the declared budget.
    // A structural bound that exceeds the declared `structural_gas` limit is a
    // budget violation: the workflow skeleton provably costs more than the
    // program reserved. (`structural_gas == 0` means "unspecified" and is not
    // enforced — the bound is still surfaced via GasAnalysis.structural_bound.)
    // See F-MEDIUM (structural-gas-limit-never-enforced).
    if program.gas_budget.structural_gas > 0 && gas_bound > program.gas_budget.structural_gas {
        errors.push(format!(
            "structural gas bound {gas_bound} exceeds declared budget {}",
            program.gas_budget.structural_gas
        ));
    }

    // Deterministic diagnostic order: a BTreeSet sorts names lexicographically
    // so replay runs emit the violations list in stable sequence. This backs
    // the replay-determinism claim in the op-core proof-bundle contract.
    //
    // Real linearity/affinity violations are accumulated during the walk in
    // `ctx.linearity_violations` (double-consume, use-after-consume,
    // access-while-locked, lock-after-consume, re-lock-after-spend). The old
    // `consumed_linears ∩ locked` intersection was structurally always empty
    // and reported nothing. See F1.
    let linearity_sorted: BTreeSet<String> = ctx.linearity_violations.clone();
    let asymmetric_obligations: Vec<String> = {
        let mut v = ctx.branch_asymmetric_consumptions.clone();
        v.sort();
        v.dedup();
        v
    };
    TypeCheckResult {
        success: errors.is_empty(),
        inferred_type: Some(serde_json::to_string(&program.outputs).unwrap_or_default()),
        discharged_predicates: discharged,
        deferred_predicates: deferred,
        failed_predicates: failed,
        linearity_violations: linearity_sorted.into_iter().collect(),
        asymmetric_consumption_obligations: asymmetric_obligations,
        gas_analysis: Some(GasAnalysis {
            structural_bound: gas_bound,
            needs_cardinality_cert: program.gas_budget.per_element_gas > 0
                && program.gas_budget.cardinality_certificate.is_none(),
            max_extensional_gas: extensional_bound,
        }),
        errors,
    }
}

fn program_output_type(outputs: &[(String, OpType)]) -> Option<OpType> {
    match outputs {
        [] => None,
        [(_, ty)] => Some(ty.clone()),
        fields => Some(OpType::Record(fields.to_vec())),
    }
}

fn block_contains_return(stmts: &[Statement]) -> bool {
    stmts.iter().any(statement_contains_return)
}

fn statement_contains_return(stmt: &Statement) -> bool {
    match stmt {
        Statement::Return(_) => true,
        Statement::Choose { arms, else_block } => {
            arms.iter().any(|(_, body)| block_contains_return(body))
                || else_block
                    .as_ref()
                    .is_some_and(|body| block_contains_return(body))
        }
        Statement::In { body, .. } => block_contains_return(body),
        Statement::Step(step) => match &step.body {
            StepBody::Block(inner) => block_contains_return(inner),
            StepBody::Primitive(_, _) => false,
        },
        _ => false,
    }
}

fn initializer_compatible(annotation: &OpType, actual: &OpType) -> bool {
    annotation == actual
        || matches!(annotation, OpType::Linear(inner) if inner.as_ref() == actual)
        || matches!(actual, OpType::Linear(inner) if inner.as_ref() == annotation)
}

/// Choose the binding type for a `let` so that linearity is never erased by a
/// looser annotation. If either the annotation or the inferred type is
/// `Linear<T>` over the same inner type, bind the `Linear<T>` form: a resource
/// the initializer produced linearly must remain linear in scope even if the
/// author wrote the bare inner type, and a resource the author declared linear
/// stays linear even if the initializer inferred bare. Otherwise bind the
/// annotation (the author's intent). See F-MEDIUM (initializer-compatible-asymmetry).
fn binding_type_preserving_linearity(annotation: &OpType, actual: &OpType) -> OpType {
    match (annotation, actual) {
        (OpType::Linear(_), _) => annotation.clone(),
        (_, OpType::Linear(inner)) if inner.as_ref() == annotation => actual.clone(),
        _ => annotation.clone(),
    }
}

fn check_block(
    stmts: &[Statement],
    ctx: &mut TypeContext,
    errors: &mut Vec<String>,
    discharged: &mut Vec<SafetyPredicate>,
    deferred: &mut Vec<SafetyPredicate>,
    failed: &mut Vec<SafetyPredicateFailure>,
    expected_return: Option<&OpType>,
) {
    for stmt in stmts {
        check_statement(
            stmt,
            ctx,
            errors,
            discharged,
            deferred,
            failed,
            expected_return,
        );
    }
}

fn check_statement(
    stmt: &Statement,
    ctx: &mut TypeContext,
    errors: &mut Vec<String>,
    discharged: &mut Vec<SafetyPredicate>,
    deferred: &mut Vec<SafetyPredicate>,
    failed: &mut Vec<SafetyPredicateFailure>,
    expected_return: Option<&OpType>,
) {
    match stmt {
        Statement::Let { name, ty, value } => {
            check_expression_site(value, ctx, errors, failed, &format!("in let {name}"));
            // Bind the linearity-preserving type so an annotation cannot hide a
            // linear initializer (and downstream double-use stays detectable).
            let mut bound_ty = ty.clone();
            match static_expr_type(value, ctx) {
                Ok(actual) if initializer_compatible(ty, &actual) => {
                    bound_ty = binding_type_preserving_linearity(ty, &actual);
                }
                Ok(actual) => errors.push(format!(
                    "let `{name}` initializer type {actual:?} does not match annotation {ty:?}"
                )),
                Err(err) => errors.push(format!("in let {name} type inference: {err}")),
            }
            ctx.bind(name.clone(), bound_ty);
        }
        Statement::Run { name, call } => {
            check_expression_site(call, ctx, errors, failed, &format!("in run {name}"));
            // The shape of a primitive call's return type is
            // host-determined; we bind to a record placeholder.
            ctx.bind(name.clone(), OpType::Record(vec![]));
        }
        Statement::Step(step) => {
            match &step.body {
                StepBody::Primitive(_, args) => {
                    for (_, arg) in args {
                        check_expression_site(
                            arg,
                            ctx,
                            errors,
                            failed,
                            &format!("in step {}", step.id),
                        );
                    }
                }
                StepBody::Block(inner) => {
                    let mut inner_ctx = ctx.clone();
                    check_block(
                        inner,
                        &mut inner_ctx,
                        errors,
                        discharged,
                        deferred,
                        failed,
                        Some(&step.signature.output),
                    );
                    if step.signature.output != OpType::Unit && !block_contains_return(inner) {
                        errors.push(format!(
                            "step `{}` declares output {:?} but block body contains no return",
                            step.id, step.signature.output
                        ));
                    }
                }
            }
            if let Some(comp) = &step.compensate {
                if let StepBody::Block(inner) = &comp.body {
                    let mut inner_ctx = ctx.clone();
                    check_block(
                        inner,
                        &mut inner_ctx,
                        errors,
                        discharged,
                        deferred,
                        failed,
                        Some(&OpType::Unit),
                    );
                }
                if let StepBody::Primitive(_, args) = &comp.body {
                    for (_, arg) in args {
                        check_expression_site(
                            arg,
                            ctx,
                            errors,
                            failed,
                            &format!("in compensate of step {}", step.id),
                        );
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
                check_expression_site(
                    e,
                    &mut sub,
                    errors,
                    failed,
                    &format!("in par branch {name}"),
                );
                branch_ctxs.push(sub);
                ctx.bind(name.clone(), OpType::Record(vec![]));
            }
            ctx.reconcile_branches(&branch_ctxs);
        }
        Statement::Choose { arms, else_block } => {
            let mut branch_ctxs: Vec<TypeContext> = Vec::new();
            for (guard, block) in arms {
                check_expression_site(guard, ctx, errors, failed, "in choose guard");
                let mut sub = ctx.clone();
                check_block(
                    block,
                    &mut sub,
                    errors,
                    discharged,
                    deferred,
                    failed,
                    expected_return,
                );
                branch_ctxs.push(sub);
            }
            if let Some(else_body) = else_block {
                let mut sub = ctx.clone();
                check_block(
                    else_body,
                    &mut sub,
                    errors,
                    discharged,
                    deferred,
                    failed,
                    expected_return,
                );
                branch_ctxs.push(sub);
            }
            ctx.reconcile_branches(&branch_ctxs);
        }
        Statement::In { body, .. } => {
            check_block(
                body,
                ctx,
                errors,
                discharged,
                deferred,
                failed,
                expected_return,
            );
        }
        Statement::Policy { name, domains } => {
            errors.push(format!(
                "policy block `{name}` over domains {domains:?} requires a verified proof receipt"
            ));
        }
        Statement::Return(e) => {
            check_expression_site(e, ctx, errors, failed, "in expression");
            if let Some(expected) = expected_return {
                match static_expr_type(e, ctx) {
                    Ok(actual) if &actual == expected => {}
                    Ok(actual) => errors.push(format!(
                        "return type {actual:?} does not match declared output {expected:?}"
                    )),
                    Err(err) => errors.push(format!("in return type inference: {err}")),
                }
            }
        }
        Statement::Expr(e) => {
            check_expression_site(e, ctx, errors, failed, "in expression");
        }
    }
}

fn check_expression_site(
    expr: &OpExpr,
    ctx: &mut TypeContext,
    errors: &mut Vec<String>,
    failed: &mut Vec<SafetyPredicateFailure>,
    site: &str,
) {
    if let Err(e) = check_expr(expr, ctx) {
        errors.push(format!("{site}: {e}"));
    }
    record_safety_assertions(expr, failed, errors, site);
}

fn check_expr(expr: &OpExpr, ctx: &mut TypeContext) -> Result<(), String> {
    match expr {
        OpExpr::Unit | OpExpr::Bool(_) | OpExpr::Int(_) | OpExpr::String(_) | OpExpr::Null => {
            Ok(())
        }
        OpExpr::Var(name) => {
            if ctx.lookup(name).is_some() {
                if ctx.consumed_linears.contains(name) {
                    ctx.record_linearity_violation(name);
                    return Err(format!(
                        "linear-use-after-consume: {name} was consumed earlier in this branch"
                    ));
                }
                // A `Locked<T>` is affine with EXACTLY two eliminators
                // (commit_transfer, release_lock). A bare `Var` reference to a
                // locked resource is direct access that bypasses both — forbid
                // it. See F2.
                if ctx.is_locked(name) {
                    ctx.record_linearity_violation(name);
                    return Err(format!(
                        "locked-resource-access: {name} is locked and may only be eliminated by \
                         commit_transfer or release_lock"
                    ));
                }
                Ok(())
            } else {
                Err(format!("unbound variable: {name}"))
            }
        }
        OpExpr::Field(base, _field) => {
            // Field access of a locked underlying resource is still access to
            // the locked resource and must be rejected — the `Locked<T>`
            // wrapper cannot be peeled by projection. See F4. (The recursive
            // `check_expr(base)` below also catches a bare locked `Var`, but we
            // reject explicitly on the underlying name to give a precise
            // diagnostic even through nested projection.)
            if let Some(n) = underlying_var(base) {
                if ctx.is_locked(&n) {
                    ctx.record_linearity_violation(&n);
                    return Err(format!(
                        "locked-resource-access: field access of locked resource '{n}' is not \
                         permitted; eliminate it with commit_transfer or release_lock"
                    ));
                }
            }
            check_expr(base, ctx)
        }
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
            check_expr(b, ctx)?;
            if let OpExpr::BinOp(op, _, _) = expr {
                let left = static_expr_type(a, ctx)?;
                let right = static_expr_type(b, ctx)?;
                check_binop_types(*op, &left, &right)?;
            }
            Ok(())
        }
        OpExpr::Seq(a, b) => {
            // Seq evaluates `a` for its effect, returns `b`'s value.
            // Type of a Seq expression is the type of its second operand.
            check_expr(a, ctx)?;
            check_expr(b, ctx)
        }
        OpExpr::UnOp(op, a) => {
            check_expr(a, ctx)?;
            let ty = static_expr_type(a, ctx)?;
            match op {
                UnOp::Not if ty == OpType::Bool => Ok(()),
                UnOp::Neg if ty == OpType::Int => Ok(()),
                _ => Err(format!("{op:?} operand has incompatible type {ty:?}")),
            }
        }
        OpExpr::Await { .. } => Ok(()),
        OpExpr::Match {
            scrutinee,
            arms,
            catch_all,
        } => {
            check_expr(scrutinee, ctx)?;
            let scrutinee_ty = static_expr_type(scrutinee, ctx)?;
            validate_match_patterns(&scrutinee_ty, arms)?;
            // First validate each arm/catch-all body in its own binding scope,
            // collecting the arm types (with their pattern labels for
            // diagnostics). The result type is then the JOIN of all arm types:
            // a variant-arm least-upper-bound when every arm is a variant (the
            // defeasible-rule case — see `join_variant_arm_types`), and the
            // legacy structural-equality rule otherwise.
            let mut arm_types: Vec<(String, OpType)> = Vec::with_capacity(arms.len() + 1);
            for arm in arms {
                let mut sub = ctx.clone();
                if !arm.binding.is_empty() && arm.binding != "_" {
                    sub.bind(
                        arm.binding.clone(),
                        match_binding_type(&scrutinee_ty, &arm.pattern)?,
                    );
                }
                check_expr(&arm.body, &mut sub)?;
                arm_types.push((arm.pattern.clone(), static_expr_type(&arm.body, &sub)?));
            }
            check_expr(catch_all, ctx)?;
            arm_types.push(("<catch-all>".to_string(), static_expr_type(catch_all, ctx)?));
            // Validate that the arm types have a well-formed join (variant union
            // or structural agreement); discard the joined type here — the
            // synthesized type is produced by `static_expr_type`'s mirror call.
            join_match_arm_types(&arm_types)?;
            Ok(())
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
                    ctx.record_linearity_violation(n);
                    return Err(format!(
                        "linear-use-after-consume: {n} cannot be locked after consumption"
                    ));
                }
                if ctx.is_locked(n) {
                    ctx.record_linearity_violation(n);
                    return Err(format!(
                        "double-lock: {n} is already locked and cannot be locked again"
                    ));
                }
                // The lock capability is single-use (affine). Once a name's
                // lock was committed or released, it can never be re-locked —
                // otherwise lock/release/lock/commit would let one linear
                // resource be transferred across two corridors. See F6.
                if ctx.lock_spent.contains(n) {
                    ctx.record_linearity_violation(n);
                    return Err(format!(
                        "lock-after-release: {n} had its lock capability spent (committed or \
                         released) and cannot be locked again"
                    ));
                }
                ctx.lock(n);
                Ok(())
            } else {
                check_expr(resource, ctx)
            }
        }
        OpExpr::CommitTransfer { locked, witness } => {
            // The lock check must hold regardless of how the locked handle is
            // wrapped. `commit_transfer(account.lock_handle, w)` or
            // `commit_transfer({h: x}, w)` must NOT bypass the locked-resource
            // requirement. Find the locked variable underneath any
            // Field/Record/Call/Var wrapping and enforce on it. See F3.
            let target = locked_target(locked, ctx).ok_or_else(|| {
                format!(
                    "commit_transfer requires a locked resource; none of the referenced \
                     resources {:?} are locked",
                    referenced_vars(locked)
                )
            })?;
            // Committing consumes the linear resource underlying the lock, AND
            // eliminates the Locked<T> wrapper, AND spends the lock capability
            // so the name can never be re-locked. See F3/F4/F6.
            ctx.consume_linear(&target).map_err(|e| e.to_string())?;
            ctx.locked.remove(&target);
            ctx.lock_spent.insert(target);
            check_expr(witness, ctx)
        }
        OpExpr::ReleaseLock { locked, witness } => {
            let target = locked_target(locked, ctx).ok_or_else(|| {
                format!(
                    "release_lock requires a locked resource; none of the referenced \
                     resources {:?} are locked",
                    referenced_vars(locked)
                )
            })?;
            // Release restores Locked<T> to Linear<T>; the linear is *not*
            // consumed. Remove the locked-wrapper name and spend the lock
            // capability so the released lock can never be re-acquired. See
            // F3/F4/F6.
            ctx.locked.remove(&target);
            ctx.lock_spent.insert(target);
            check_expr(witness, ctx)
        }
    }
}

/// The underlying variable an expression *directly* names, peeling
/// single-resource wrappers. Used to detect locked-resource access through
/// projection/consumption. Multi-resource wrappers (Record with several
/// fields, Call with several args) return `None` here — use
/// [`referenced_vars`] for those.
fn underlying_var(expr: &OpExpr) -> Option<String> {
    match expr {
        OpExpr::Var(n) => Some(n.clone()),
        OpExpr::Field(base, _) => underlying_var(base),
        OpExpr::ConsumeLinear(inner) => underlying_var(inner),
        OpExpr::Lock { resource, .. } => underlying_var(resource),
        OpExpr::CommitTransfer { locked, .. } | OpExpr::ReleaseLock { locked, .. } => {
            underlying_var(locked)
        }
        _ => None,
    }
}

/// Every variable name referenced anywhere inside an expression tree. Used to
/// locate a locked resource through arbitrary Field/Record/Call wrapping so the
/// lock check cannot be bypassed by indirection. See F3.
fn referenced_vars(expr: &OpExpr) -> BTreeSet<String> {
    let mut acc = BTreeSet::new();
    collect_referenced_vars(expr, &mut acc);
    acc
}

fn collect_referenced_vars(expr: &OpExpr, acc: &mut BTreeSet<String>) {
    match expr {
        OpExpr::Var(n) => {
            acc.insert(n.clone());
        }
        OpExpr::Field(base, _) => collect_referenced_vars(base, acc),
        OpExpr::Record(fields) => {
            for (_, e) in fields {
                collect_referenced_vars(e, acc);
            }
        }
        OpExpr::Call(_, args) => {
            for (_, e) in args {
                collect_referenced_vars(e, acc);
            }
        }
        OpExpr::List(items) | OpExpr::Tuple(items) => {
            for e in items {
                collect_referenced_vars(e, acc);
            }
        }
        OpExpr::BinOp(_, a, b) | OpExpr::Coalesce(a, b) | OpExpr::Seq(a, b) => {
            collect_referenced_vars(a, acc);
            collect_referenced_vars(b, acc);
        }
        OpExpr::UnOp(_, a) | OpExpr::ConsumeLinear(a) => collect_referenced_vars(a, acc),
        OpExpr::Lock { resource, .. } => collect_referenced_vars(resource, acc),
        OpExpr::CommitTransfer { locked, witness } | OpExpr::ReleaseLock { locked, witness } => {
            collect_referenced_vars(locked, acc);
            collect_referenced_vars(witness, acc);
        }
        OpExpr::Match {
            scrutinee,
            arms,
            catch_all,
        } => {
            collect_referenced_vars(scrutinee, acc);
            for arm in arms {
                collect_referenced_vars(&arm.body, acc);
            }
            collect_referenced_vars(catch_all, acc);
        }
        OpExpr::Unit
        | OpExpr::Bool(_)
        | OpExpr::Int(_)
        | OpExpr::String(_)
        | OpExpr::Null
        | OpExpr::AssertSafety(_)
        | OpExpr::Await { .. } => {}
    }
}

/// Find the locked resource an eliminator (`commit_transfer`/`release_lock`)
/// operates on, looking through any Field/Record/Call/Var wrapping. Returns the
/// single locked variable if exactly one referenced variable is locked. If more
/// than one referenced variable is locked the eliminator is ambiguous and we
/// fail closed (`None` → caller rejects), because eliminating the wrong one (or
/// silently both) would corrupt the affine accounting. See F3.
fn locked_target(expr: &OpExpr, ctx: &TypeContext) -> Option<String> {
    // Fast path: a directly-named locked variable (Var or single-resource
    // projection) — the common, unambiguous case.
    if let Some(n) = underlying_var(expr) {
        if ctx.is_locked(&n) {
            return Some(n);
        }
    }
    // Wrapped path: scan every referenced variable for a locked one.
    let locked_refs: Vec<String> = referenced_vars(expr)
        .into_iter()
        .filter(|n| ctx.is_locked(n))
        .collect();
    match locked_refs.as_slice() {
        [single] => Some(single.clone()),
        _ => None, // zero locked (reject: not locked) or ambiguous (fail closed)
    }
}

fn check_binop_types(op: BinOp, left: &OpType, right: &OpType) -> Result<(), String> {
    match op {
        BinOp::And | BinOp::Or => require_operands(op, left, right, &OpType::Bool),
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Add | BinOp::Sub | BinOp::Mul => {
            require_operands(op, left, right, &OpType::Int)
        }
        BinOp::Eq | BinOp::Ne => {
            if left == right {
                Ok(())
            } else {
                Err(format!(
                    "{op:?} operands must have the same type, got {left:?} and {right:?}"
                ))
            }
        }
        BinOp::In => match right {
            OpType::List(inner) if inner.as_ref() == left => Ok(()),
            _ => Err(format!(
                "In expects right operand List<{left:?}>, got {right:?}"
            )),
        },
        BinOp::Contains => match left {
            OpType::List(inner) if inner.as_ref() == right => Ok(()),
            OpType::String if matches!(right, OpType::String) => Ok(()),
            _ => Err(format!(
                "Contains expects List<T>, T or String, String, got {left:?} and {right:?}"
            )),
        },
    }
}

fn require_operands(
    op: BinOp,
    left: &OpType,
    right: &OpType,
    expected: &OpType,
) -> Result<(), String> {
    if left == expected && right == expected {
        Ok(())
    } else {
        Err(format!(
            "{op:?} operands must both be {expected:?}, got {left:?} and {right:?}"
        ))
    }
}

fn op_verdict_variant() -> OpType {
    OpType::Variant(vec![
        ("Compliant".to_string(), OpType::Unit),
        (
            "NonCompliant".to_string(),
            OpType::Record(vec![("reason".to_string(), OpType::String)]),
        ),
        ("SanctionsBlocked".to_string(), OpType::Unit),
    ])
}

fn static_expr_type(expr: &OpExpr, ctx: &TypeContext) -> Result<OpType, String> {
    match expr {
        OpExpr::Unit => Ok(OpType::Unit),
        OpExpr::Bool(_) => Ok(OpType::Bool),
        OpExpr::Int(_) => Ok(OpType::Int),
        OpExpr::String(_) => Ok(OpType::String),
        OpExpr::Null => Ok(OpType::Option(Box::new(OpType::Unit))),
        OpExpr::Var(name) => ctx
            .lookup(name)
            .cloned()
            .ok_or_else(|| format!("unbound variable: {name}")),
        OpExpr::Field(base, field) => match static_expr_type(base, ctx)? {
            OpType::Record(fields) => fields
                .into_iter()
                .find_map(|(name, ty)| (name == *field).then_some(ty))
                .ok_or_else(|| format!("unknown record field: {field}")),
            other => Err(format!("field access on non-record type: {other:?}")),
        },
        OpExpr::Record(fields) => {
            let field_types = fields
                .iter()
                .map(|(name, value)| Ok((name.clone(), static_expr_type(value, ctx)?)))
                .collect::<Result<Vec<_>, String>>()?;
            // An encoded `{tag: "Ctor", value: V}` record denotes ONE variant
            // case. The old code typed it as `Variant(vec![])` — an empty
            // constructor list — which made every `match` on it vacuously
            // exhaustive (no constructor to cover). Populate the actual single
            // constructor from the literal tag and the value's type, so a match
            // on this value must cover that constructor. See F8.
            if is_encoded_variant_record(fields) {
                let tag = encoded_variant_tag(fields).ok_or_else(|| {
                    "encoded variant record `tag` must be a string literal".to_string()
                })?;
                let value_ty = field_types
                    .iter()
                    .find_map(|(n, ty)| (n == "value").then(|| ty.clone()))
                    .unwrap_or(OpType::Unit);
                Ok(OpType::Variant(vec![(tag, value_ty)]))
            } else {
                Ok(OpType::Record(field_types))
            }
        }
        OpExpr::List(items) => {
            let mut item_ty: Option<OpType> = None;
            for item in items {
                let ty = static_expr_type(item, ctx)?;
                if let Some(expected) = &item_ty {
                    if expected != &ty {
                        return Err(format!(
                            "list item type mismatch: expected {expected:?}, got {ty:?}"
                        ));
                    }
                } else {
                    item_ty = Some(ty);
                }
            }
            Ok(OpType::List(Box::new(item_ty.unwrap_or(OpType::Unit))))
        }
        OpExpr::Tuple(items) => items
            .iter()
            .map(|item| static_expr_type(item, ctx))
            .collect::<Result<Vec<_>, _>>()
            .map(OpType::Tuple),
        OpExpr::Call(name, _) => match name.as_str() {
            "sanctions.check" => Ok(op_verdict_variant()),
            "attestation.append" => Ok(OpType::Record(vec![])),
            // An unknown primitive has a host-determined return shape the
            // checker cannot know. Silently typing it as an empty record let
            // any downstream type flow through unchecked (e.g. a match on its
            // result would see no constructors and skip exhaustiveness). Fail
            // loud instead of fabricating a type. See F9. (`Statement::Run` /
            // `Statement::Par` still bind a record placeholder explicitly for
            // the host-determined call result; they do not route through this
            // inference path.)
            other => Err(format!(
                "cannot infer the type of unknown primitive call `{other}`; \
                 its return type is host-determined and must be bound via `run`/`par`, \
                 not used directly in a type-inference position"
            )),
        },
        OpExpr::BinOp(op, left, right) => {
            let left_ty = static_expr_type(left, ctx)?;
            let right_ty = static_expr_type(right, ctx)?;
            check_binop_types(*op, &left_ty, &right_ty)?;
            Ok(match op {
                BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::And
                | BinOp::Or
                | BinOp::In
                | BinOp::Contains => OpType::Bool,
                BinOp::Add | BinOp::Sub | BinOp::Mul => OpType::Int,
            })
        }
        OpExpr::UnOp(op, inner) => {
            let inner_ty = static_expr_type(inner, ctx)?;
            match op {
                UnOp::Not if inner_ty == OpType::Bool => Ok(OpType::Bool),
                UnOp::Neg if inner_ty == OpType::Int => Ok(OpType::Int),
                _ => Err(format!("{op:?} operand has incompatible type {inner_ty:?}")),
            }
        }
        OpExpr::Coalesce(left, _right) => static_expr_type(left, ctx),
        OpExpr::Seq(_left, right) => static_expr_type(right, ctx),
        OpExpr::Await { event, .. } => Ok(OpType::Await {
            event: event.clone(),
            payload: Box::new(OpType::Record(vec![])),
        }),
        OpExpr::Match {
            scrutinee,
            arms,
            catch_all,
        } => {
            let scrutinee_ty = static_expr_type(scrutinee, ctx)?;
            validate_match_patterns(&scrutinee_ty, arms)?;
            let mut arm_types: Vec<(String, OpType)> = Vec::with_capacity(arms.len() + 1);
            for arm in arms {
                let mut sub = ctx.clone();
                if !arm.binding.is_empty() && arm.binding != "_" {
                    sub.bind(
                        arm.binding.clone(),
                        match_binding_type(&scrutinee_ty, &arm.pattern)?,
                    );
                }
                arm_types.push((arm.pattern.clone(), static_expr_type(&arm.body, &sub)?));
            }
            arm_types.push(("<catch-all>".to_string(), static_expr_type(catch_all, ctx)?));
            // The match result type is the JOIN (least-upper-bound) of all arm
            // types: the variant-union when every arm is a variant, and the
            // legacy structural-equality result otherwise. Mirrors the same
            // call in `check_expr`.
            join_match_arm_types(&arm_types)
        }
        OpExpr::AssertSafety(_) => Ok(OpType::Unit),
        OpExpr::ConsumeLinear(inner) => static_expr_type(inner, ctx),
        OpExpr::Lock { resource, .. } => {
            Ok(OpType::Locked(Box::new(static_expr_type(resource, ctx)?)))
        }
        // commit_transfer destructures the `Locked<T>` wrapper and yields the
        // committed value `T`. release_lock destructures `Locked<Linear<T>>`
        // back to the unconsumed `Linear<T>`. Returning the `Locked<…>` wrapper
        // itself (the old behaviour) was unsound: the result would still type
        // as locked, so a single lock could be eliminated and then the
        // "result" eliminated again. See F5.
        OpExpr::CommitTransfer { locked, .. } => {
            let inner = static_expr_type(locked, ctx)?;
            Ok(committed_value_type(&inner))
        }
        OpExpr::ReleaseLock { locked, .. } => {
            let inner = static_expr_type(locked, ctx)?;
            Ok(released_linear_type(&inner))
        }
    }
}

/// Destructure a locked handle's type to the value produced by committing it.
/// `Locked<Linear<T>>` → `T`; `Locked<T>` → `T`; `Linear<T>` → `T` (a Var bound
/// `Linear<T>` whose lock state lives in the lock set, not the binding); any
/// other type is returned unchanged (best-effort; the affinity check in
/// `check_expr` is what enforces the lock requirement). See F5.
fn committed_value_type(handle: &OpType) -> OpType {
    match handle {
        OpType::Locked(inner) => committed_value_type(inner),
        OpType::Linear(inner) => inner.as_ref().clone(),
        other => other.clone(),
    }
}

/// Destructure a locked handle's type back to the `Linear<T>` that releasing it
/// restores. `Locked<Linear<T>>` → `Linear<T>`; `Locked<T>` → `Linear<T>`;
/// `Linear<T>` → `Linear<T>` (already restored shape). See F5.
fn released_linear_type(handle: &OpType) -> OpType {
    match handle {
        OpType::Locked(inner) => released_linear_type(inner),
        linear @ OpType::Linear(_) => linear.clone(),
        other => OpType::Linear(Box::new(other.clone())),
    }
}

fn is_encoded_variant_record(fields: &[(String, OpExpr)]) -> bool {
    matches!(
        fields,
        [
            (tag_name, OpExpr::String(_)),
            (value_name, _)
        ] if tag_name == "tag" && value_name == "value"
    )
}

/// Extract the literal constructor tag from an encoded variant record
/// `{tag: "Ctor", value: V}`. See F8.
fn encoded_variant_tag(fields: &[(String, OpExpr)]) -> Option<String> {
    match fields {
        [(tag_name, OpExpr::String(tag)), (value_name, _)]
            if tag_name == "tag" && value_name == "value" =>
        {
            Some(tag.clone())
        }
        _ => None,
    }
}

/// Least-upper-bound (join) of `match` arm types in the variant subtyping
/// lattice.
///
/// A `match` whose arms produce different *constructors* of the same variant
/// datatype (the defeasible-rule lowering `match guard { true -> NonCompliant;
/// false -> Compliant }`) is well-typed: the result is the **union** of all arm
/// constructor sets. Each arm is a subtype of that union (widening a singleton
/// `Variant([C])` to `Variant([C, D, ...])` over the same datatype is sound —
/// every value of the arm type is a value of the union), so the union is the
/// supremum of the arm types and a program declaring `outputs: Variant([C, D,
/// ...])` (e.g. the full `Verdict` constructor set) accepts it.
///
/// Discipline (this is a JOIN, not a silent merge):
///
/// * All arm types must be `Variant(_)` to take the union path. If any arm is a
///   non-variant type, the join falls back to structural equality — a `Bool`
///   arm next to an `Int` arm is a genuine error, and a non-variant arm next to
///   a variant arm is a genuine error, both surfaced as the existing
///   "different types" diagnostic by the caller.
/// * SOUNDNESS CONDITION (fail-loud): a constructor `tag` present in more than
///   one arm MUST carry the **same** payload type in every occurrence. A tag
///   reused with conflicting payloads (`C(Int)` vs `C(String)`) is a real
///   `TypeError` — never silently coerced, never resolved by picking one side.
/// * The union is keyed by a `BTreeMap`, so the resulting constructor list is
///   sorted by tag name — deterministic, so the compiler's mirror inference
///   (`op-lex-compiler::infer_expr_type`) and this checker agree byte-for-byte
///   on the declared/inferred output type.
///
/// Returns `Ok(None)` when the arm types are NOT all variants (signalling the
/// caller to apply the legacy structural-equality rule), `Ok(Some(join))` when
/// the variant union is well-formed, and `Err` on a payload conflict.
fn join_variant_arm_types(arm_types: &[OpType]) -> Result<Option<OpType>, String> {
    if arm_types.is_empty() {
        return Ok(None);
    }
    // Union only applies when every arm is a variant. Otherwise the caller's
    // structural-equality rule handles it (including the genuine error of
    // mixing a variant arm with a non-variant arm).
    let all_variants = arm_types
        .iter()
        .all(|t| matches!(t, OpType::Variant(_)));
    if !all_variants {
        return Ok(None);
    }

    // Accumulate the constructor union. A tag seen twice must agree on payload.
    let mut union: BTreeMap<String, OpType> = BTreeMap::new();
    for ty in arm_types {
        if let OpType::Variant(constructors) = ty {
            for (tag, payload_ty) in constructors {
                match union.get(tag) {
                    Some(existing) if existing != payload_ty => {
                        return Err(format!(
                            "match arms assign conflicting payload types to constructor \
                             `{tag}`: {existing:?} vs {payload_ty:?}"
                        ));
                    }
                    Some(_) => {}
                    None => {
                        union.insert(tag.clone(), payload_ty.clone());
                    }
                }
            }
        }
    }

    Ok(Some(OpType::Variant(union.into_iter().collect())))
}

/// Compute the result type of a `match` from its labeled arm types (each arm
/// plus the catch-all, the catch-all labeled `<catch-all>`).
///
/// * If every arm is a variant, the result is the constructor-set union
///   (`join_variant_arm_types`), failing loud on a payload conflict.
/// * Otherwise the legacy rule applies: all arm types must be structurally
///   equal, and the first divergent arm is reported with its pattern label
///   (preserving the existing `match arm ... has type ...` / `match catch-all
///   has type ...` diagnostics, so non-variant mismatches and variant/
///   non-variant mixes are rejected exactly as before).
///
/// `arm_types` is never empty in practice (the catch-all is always pushed);
/// an empty slice degenerates to `Unit`.
fn join_match_arm_types(arm_types: &[(String, OpType)]) -> Result<OpType, String> {
    let only_types: Vec<OpType> = arm_types.iter().map(|(_, t)| t.clone()).collect();
    if let Some(joined) = join_variant_arm_types(&only_types)? {
        return Ok(joined);
    }
    // Legacy structural-equality path (non-variant arms, or a variant mixed
    // with a non-variant — both genuine errors when they disagree).
    let mut expected: Option<OpType> = None;
    for (label, ty) in arm_types {
        match &expected {
            Some(exp) if exp != ty => {
                if label == "<catch-all>" {
                    return Err(format!(
                        "match catch-all has type {ty:?}, expected {exp:?}"
                    ));
                }
                return Err(format!(
                    "match arm `{label}` has type {ty:?}, expected {exp:?}"
                ));
            }
            Some(_) => {}
            None => expected = Some(ty.clone()),
        }
    }
    Ok(expected.unwrap_or(OpType::Unit))
}

fn match_binding_type(scrutinee_ty: &OpType, pattern: &str) -> Result<OpType, String> {
    match scrutinee_ty {
        OpType::Bool => match pattern {
            "true" | "false" => Ok(OpType::Unit),
            other => Err(format!("unknown Bool match pattern `{other}`")),
        },
        OpType::Variant(constructors) if constructors.is_empty() => Ok(OpType::Record(vec![])),
        OpType::Variant(constructors) => constructors
            .iter()
            .find_map(|(name, ty)| (name == pattern).then_some(ty.clone()))
            .ok_or_else(|| format!("unknown variant match pattern `{pattern}`")),
        other => Err(format!(
            "match scrutinee must be Bool or Variant, got {other:?}"
        )),
    }
}

fn validate_match_patterns(scrutinee_ty: &OpType, arms: &[MatchArm]) -> Result<(), String> {
    if !matches!(scrutinee_ty, OpType::Bool | OpType::Variant(_)) {
        return Err(format!(
            "match scrutinee must be Bool or Variant, got {scrutinee_ty:?}"
        ));
    }

    let mut seen = BTreeSet::new();
    for arm in arms {
        if !seen.insert(arm.pattern.clone()) {
            return Err(format!("duplicate match arm `{}`", arm.pattern));
        }
        match_binding_type(scrutinee_ty, &arm.pattern)?;
    }

    let expected: Option<Vec<String>> = match scrutinee_ty {
        OpType::Bool => Some(vec!["true".to_string(), "false".to_string()]),
        OpType::Variant(constructors) if !constructors.is_empty() => {
            Some(constructors.iter().map(|(name, _)| name.clone()).collect())
        }
        _ => None,
    };
    if let Some(expected) = expected {
        for name in expected {
            if !seen.contains(&name) {
                return Err(format!("match is missing constructor arm `{name}`"));
            }
        }
    }
    Ok(())
}

fn record_safety_assertions(
    expr: &OpExpr,
    failed: &mut Vec<SafetyPredicateFailure>,
    errors: &mut Vec<String>,
    site: &str,
) {
    match expr {
        OpExpr::AssertSafety(predicate) => {
            failed.push(SafetyPredicateFailure {
                predicate: predicate.clone(),
                reason: "bare AssertSafety carries no verified receipt".to_string(),
            });
            errors.push(format!(
                "{site}: safety predicate {predicate:?} requires a verified receipt"
            ));
        }
        OpExpr::Field(base, _) | OpExpr::UnOp(_, base) | OpExpr::ConsumeLinear(base) => {
            record_safety_assertions(base, failed, errors, site);
        }
        OpExpr::Record(fields) => {
            for (_, value) in fields {
                record_safety_assertions(value, failed, errors, site);
            }
        }
        OpExpr::List(items) | OpExpr::Tuple(items) => {
            for item in items {
                record_safety_assertions(item, failed, errors, site);
            }
        }
        OpExpr::Call(_, args) => {
            for (_, arg) in args {
                record_safety_assertions(arg, failed, errors, site);
            }
        }
        OpExpr::BinOp(_, left, right)
        | OpExpr::Coalesce(left, right)
        | OpExpr::Seq(left, right) => {
            record_safety_assertions(left, failed, errors, site);
            record_safety_assertions(right, failed, errors, site);
        }
        OpExpr::Match {
            scrutinee,
            arms,
            catch_all,
        } => {
            record_safety_assertions(scrutinee, failed, errors, site);
            for arm in arms {
                record_safety_assertions(&arm.body, failed, errors, site);
            }
            record_safety_assertions(catch_all, failed, errors, site);
        }
        OpExpr::Lock { resource, .. } => record_safety_assertions(resource, failed, errors, site),
        OpExpr::CommitTransfer { locked, witness } | OpExpr::ReleaseLock { locked, witness } => {
            record_safety_assertions(locked, failed, errors, site);
            record_safety_assertions(witness, failed, errors, site);
        }
        OpExpr::Unit
        | OpExpr::Bool(_)
        | OpExpr::Int(_)
        | OpExpr::String(_)
        | OpExpr::Null
        | OpExpr::Var(_)
        | OpExpr::Await { .. } => {}
    }
}

/// Effect-row composition: compute the union of effects reachable from the
/// program body.
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
                walk_step_body_for_effects(&step.body, acc);
                if let Some(comp) = &step.compensate {
                    walk_step_body_for_effects(&comp.body, acc);
                }
            }
            Statement::Let { value, .. } | Statement::Return(value) | Statement::Expr(value) => {
                push_expr_effects(value, acc)
            }
            Statement::Run { call, .. } => push_expr_effects(call, acc),
            Statement::Par { branches } => {
                for (_name, expr) in branches {
                    push_expr_effects(expr, acc);
                }
            }
            Statement::Choose { arms, else_block } => {
                for (g, b) in arms {
                    push_expr_effects(g, acc);
                    walk_for_effects(b, acc);
                }
                if let Some(e) = else_block {
                    walk_for_effects(e, acc);
                }
            }
            Statement::In { body, .. } => walk_for_effects(body, acc),
            Statement::Policy { .. } => {}
        }
    }
}

fn walk_step_body_for_effects(body: &StepBody, acc: &mut Vec<Effect>) {
    match body {
        StepBody::Primitive(prim, args) => {
            for e in canonical_effects_for(&prim.0) {
                acc.push(e);
            }
            for (_name, expr) in args {
                push_expr_effects(expr, acc);
            }
        }
        StepBody::Block(inner) => walk_for_effects(inner, acc),
    }
}

fn push_expr_effects(expr: &OpExpr, acc: &mut Vec<Effect>) {
    for e in expr_effects(expr).iter() {
        acc.push(e.clone());
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
    fn bare_assert_safety_fails_without_receipt() {
        let res = typecheck_program(&trivial_program(vec![Statement::Return(
            OpExpr::AssertSafety(SafetyPredicate::NoGroupFormationBypass),
        )]));
        assert!(!res.success);
        assert!(res.discharged_predicates.is_empty());
        assert_eq!(res.failed_predicates.len(), 1);
        assert!(res
            .errors
            .iter()
            .any(|e| e.contains("requires a verified receipt")));
    }

    #[test]
    fn binop_operand_types_are_checked() {
        let res = typecheck_program(&trivial_program(vec![Statement::Return(OpExpr::BinOp(
            BinOp::And,
            Box::new(OpExpr::Int(1)),
            Box::new(OpExpr::Int(2)),
        ))]));
        assert!(!res.success);
        assert!(res
            .errors
            .iter()
            .any(|e| e.contains("And operands must both be Bool")));
    }

    #[test]
    fn match_arm_result_types_must_agree() {
        let res = typecheck_program(&trivial_program(vec![Statement::Return(OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![
                MatchArm {
                    pattern: "true".to_string(),
                    binding: "_".to_string(),
                    body: OpExpr::Int(1),
                },
                MatchArm {
                    pattern: "false".to_string(),
                    binding: "_".to_string(),
                    body: OpExpr::Bool(false),
                },
            ],
            catch_all: Box::new(OpExpr::Int(0)),
        })]));
        assert!(!res.success);
        assert!(res
            .errors
            .iter()
            .any(|e| e.contains("match arm `false` has type Bool")));
    }

    #[test]
    fn declared_program_return_type_is_checked() {
        let mut prog = trivial_program(vec![Statement::Return(OpExpr::Bool(true))]);
        prog.outputs = vec![("accepted".to_string(), OpType::Bool)];
        let res = typecheck_program(&prog);
        assert!(
            res.success,
            "Bool return should satisfy Bool output: {:?}",
            res.errors
        );

        prog.body = vec![Statement::Return(OpExpr::Int(1))];
        let res = typecheck_program(&prog);
        assert!(!res.success);
        assert!(res
            .errors
            .iter()
            .any(|e| e.contains("return type Int does not match declared output Bool")));
    }

    #[test]
    fn let_initializer_must_match_annotation() {
        let res = typecheck_program(&trivial_program(vec![Statement::Let {
            name: "x".to_string(),
            ty: OpType::Bool,
            value: OpExpr::Int(1),
        }]));
        assert!(!res.success);
        assert!(res
            .errors
            .iter()
            .any(|e| e.contains("let `x` initializer type Int does not match annotation Bool")));
    }

    #[test]
    fn declared_non_unit_output_requires_return() {
        let mut prog = trivial_program(vec![Statement::Expr(OpExpr::Unit)]);
        prog.outputs = vec![("result".to_string(), OpType::Bool)];
        let res = typecheck_program(&prog);
        assert!(!res.success);
        assert!(res
            .errors
            .iter()
            .any(|e| e.contains("program declares output Bool but contains no return")));
    }

    #[test]
    fn match_catch_all_type_must_agree_with_arms() {
        let res = typecheck_program(&trivial_program(vec![Statement::Return(OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![
                MatchArm {
                    pattern: "true".to_string(),
                    binding: "_".to_string(),
                    body: OpExpr::Int(1),
                },
                MatchArm {
                    pattern: "false".to_string(),
                    binding: "_".to_string(),
                    body: OpExpr::Int(0),
                },
            ],
            catch_all: Box::new(OpExpr::Bool(false)),
        })]));
        assert!(!res.success);
        assert!(res
            .errors
            .iter()
            .any(|e| e.contains("match catch-all has type Bool, expected Int")));
    }

    #[test]
    fn match_scrutinee_must_be_bool_or_variant() {
        let res = typecheck_program(&trivial_program(vec![Statement::Return(OpExpr::Match {
            scrutinee: Box::new(OpExpr::Int(7)),
            arms: vec![],
            catch_all: Box::new(OpExpr::Unit),
        })]));
        assert!(!res.success);
        assert!(res
            .errors
            .iter()
            .any(|e| e.contains("match scrutinee must be Bool or Variant")));
    }

    #[test]
    fn bool_match_must_cover_both_constructors() {
        let res = typecheck_program(&trivial_program(vec![Statement::Return(OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![MatchArm {
                pattern: "true".to_string(),
                binding: "_".to_string(),
                body: OpExpr::Int(1),
            }],
            catch_all: Box::new(OpExpr::Int(0)),
        })]));
        assert!(!res.success);
        assert!(res
            .errors
            .iter()
            .any(|e| e.contains("match is missing constructor arm `false`")));
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

    #[test]
    fn program_effect_row_includes_expression_calls() {
        let prog = trivial_program(vec![Statement::Return(OpExpr::Call(
            "sanctions.check".to_string(),
            vec![],
        ))]);
        let row = program_effect_row(&prog);
        assert!(row.contains(&Effect::SanctionsCheck));
        assert!(row.contains(&Effect::ExternalRead));
    }

    #[test]
    fn typecheck_rejects_missing_program_effect_declaration() {
        let mut prog = trivial_program(vec![Statement::Return(OpExpr::Call(
            "sanctions.check".to_string(),
            vec![],
        ))]);
        let res = typecheck_program(&prog);
        assert!(!res.success);
        assert!(res
            .errors
            .iter()
            .any(|e| e.contains("program effect declaration missing inferred effects")));

        prog.effects = vec![Effect::SanctionsCheck, Effect::ExternalRead];
        let res = typecheck_program(&prog);
        assert!(
            res.success,
            "expected declared effects to pass: {:?}",
            res.errors
        );
    }

    // -----------------------------------------------------------------------
    // Soundness regression tests (22-agent audit closures). Each test proves a
    // confirmed linearity/affinity soundness gap is now actually enforced.
    // -----------------------------------------------------------------------

    fn linear_ctx(name: &str) -> TypeContext {
        let mut ctx = TypeContext::new();
        ctx.bind(name.to_string(), OpType::Linear(Box::new(OpType::String)));
        ctx
    }

    /// F1 — double-consume must be REPORTED in `linearity_violations`, not just
    /// rejected via an error string. (The old intersection filter was always
    /// empty so the field was never populated.) WHY: downstream tooling and
    /// proof bundles read `linearity_violations` as the canonical list of
    /// linearity faults; an always-empty list is a silent soundness hole.
    #[test]
    fn f1_double_consume_is_surfaced_in_linearity_violations() {
        let prog = trivial_program(vec![
            Statement::Let {
                name: "share".to_string(),
                ty: OpType::Linear(Box::new(OpType::String)),
                value: OpExpr::String("s".to_string()),
            },
            // Consume the same linear twice in one branch.
            Statement::Expr(OpExpr::ConsumeLinear(Box::new(OpExpr::Var(
                "share".to_string(),
            )))),
            Statement::Expr(OpExpr::ConsumeLinear(Box::new(OpExpr::Var(
                "share".to_string(),
            )))),
        ]);
        let res = typecheck_program(&prog);
        assert!(!res.success, "double-consume must fail");
        assert!(
            res.linearity_violations.contains(&"share".to_string()),
            "double-consume must be surfaced in linearity_violations, got {:?}",
            res.linearity_violations
        );
    }

    /// F1 — a clean program reports NO linearity violations (the field is not
    /// spuriously populated). WHY: a test that only checks the positive case
    /// can pass against a field that is always non-empty.
    #[test]
    fn f1_clean_program_has_no_linearity_violations() {
        let prog = trivial_program(vec![
            Statement::Let {
                name: "share".to_string(),
                ty: OpType::Linear(Box::new(OpType::String)),
                value: OpExpr::String("s".to_string()),
            },
            Statement::Expr(OpExpr::ConsumeLinear(Box::new(OpExpr::Var(
                "share".to_string(),
            )))),
        ]);
        let res = typecheck_program(&prog);
        assert!(res.success, "clean program: {:?}", res.errors);
        assert!(
            res.linearity_violations.is_empty(),
            "clean program must report no linearity violations, got {:?}",
            res.linearity_violations
        );
    }

    /// F2 — a bare `Var` reference to a locked resource is direct access that
    /// bypasses the two canonical eliminators. It must be rejected. WHY:
    /// `Locked<T>` is affine with EXACTLY two eliminators; reading it directly
    /// would let a locked resource be used while it is mid-three-phase-commit.
    #[test]
    fn f2_locked_var_direct_access_is_rejected() {
        let mut ctx = linear_ctx("share");
        let lock = OpExpr::Lock {
            resource: Box::new(OpExpr::Var("share".to_string())),
            corridor_id: "corr-a".to_string(),
        };
        assert!(check_expr(&lock, &mut ctx).is_ok());
        let direct = OpExpr::Var("share".to_string());
        let err = check_expr(&direct, &mut ctx).unwrap_err();
        assert!(
            err.contains("locked-resource-access"),
            "locked var must be rejected on direct access, got: {err}"
        );
    }

    /// F4 — field access of a locked resource must be rejected; the `Locked<T>`
    /// wrapper cannot be peeled by projection. WHY: `account.balance` where
    /// `account` is locked would otherwise read through the lock.
    #[test]
    fn f4_field_access_of_locked_resource_is_rejected() {
        let mut ctx = TypeContext::new();
        ctx.bind(
            "account".to_string(),
            OpType::Linear(Box::new(OpType::Record(vec![(
                "balance".to_string(),
                OpType::Int,
            )]))),
        );
        let lock = OpExpr::Lock {
            resource: Box::new(OpExpr::Var("account".to_string())),
            corridor_id: "corr-a".to_string(),
        };
        assert!(check_expr(&lock, &mut ctx).is_ok());
        let field = OpExpr::Field(Box::new(OpExpr::Var("account".to_string())), "balance".to_string());
        let err = check_expr(&field, &mut ctx).unwrap_err();
        assert!(
            err.contains("locked-resource-access"),
            "field access of locked resource must be rejected, got: {err}"
        );
    }

    /// F3 — the lock check must NOT be bypassable by wrapping the locked handle
    /// in a Field/Record/Call. `commit_transfer` on `{h: locked_var}` must
    /// still find the locked resource and eliminate it. WHY: an unenforced
    /// wrapped commit would leave the resource locked AND committed — double
    /// elimination.
    #[test]
    fn f3_commit_through_wrapper_still_eliminates_lock() {
        let mut ctx = linear_ctx("share");
        let lock = OpExpr::Lock {
            resource: Box::new(OpExpr::Var("share".to_string())),
            corridor_id: "corr-a".to_string(),
        };
        assert!(check_expr(&lock, &mut ctx).is_ok());
        assert!(ctx.is_locked("share"));
        // Commit through a Record wrapper.
        let commit = OpExpr::CommitTransfer {
            locked: Box::new(OpExpr::Record(vec![(
                "h".to_string(),
                OpExpr::Var("share".to_string()),
            )])),
            witness: Box::new(OpExpr::Unit),
        };
        assert!(
            check_expr(&commit, &mut ctx).is_ok(),
            "commit through wrapper of a locked resource must succeed"
        );
        // The lock was actually eliminated and the linear consumed.
        assert!(!ctx.is_locked("share"), "wrapper-commit must clear the lock");
        assert!(ctx.is_consumed("share"), "wrapper-commit must consume the linear");
        // A second elimination through the same wrapper must now fail (no
        // locked resource remains) — proving the first commit was not a no-op.
        let commit_again = OpExpr::CommitTransfer {
            locked: Box::new(OpExpr::Record(vec![(
                "h".to_string(),
                OpExpr::Var("share".to_string()),
            )])),
            witness: Box::new(OpExpr::Unit),
        };
        assert!(
            check_expr(&commit_again, &mut ctx).is_err(),
            "double commit through wrapper must be rejected"
        );
    }

    /// F3 — commit_transfer on a wrapper that references NO locked resource is
    /// rejected (it does not silently pass). WHY: the eliminator's whole point
    /// is to consume a locked resource; an unlocked argument is a type error.
    #[test]
    fn f3_commit_through_wrapper_without_lock_is_rejected() {
        let mut ctx = linear_ctx("share");
        // `share` is NOT locked.
        let commit = OpExpr::CommitTransfer {
            locked: Box::new(OpExpr::Record(vec![(
                "h".to_string(),
                OpExpr::Var("share".to_string()),
            )])),
            witness: Box::new(OpExpr::Unit),
        };
        let err = check_expr(&commit, &mut ctx).unwrap_err();
        assert!(
            err.contains("requires a locked resource"),
            "wrapped commit of an unlocked resource must be rejected, got: {err}"
        );
    }

    /// F3 — release_lock through a Field wrapper still eliminates the lock.
    #[test]
    fn f3_release_through_field_wrapper_still_eliminates_lock() {
        let mut ctx = TypeContext::new();
        ctx.bind(
            "account".to_string(),
            OpType::Linear(Box::new(OpType::Record(vec![(
                "h".to_string(),
                OpType::String,
            )]))),
        );
        let lock = OpExpr::Lock {
            resource: Box::new(OpExpr::Var("account".to_string())),
            corridor_id: "corr-a".to_string(),
        };
        assert!(check_expr(&lock, &mut ctx).is_ok());
        let release = OpExpr::ReleaseLock {
            locked: Box::new(OpExpr::Field(
                Box::new(OpExpr::Var("account".to_string())),
                "h".to_string(),
            )),
            witness: Box::new(OpExpr::Unit),
        };
        assert!(
            check_expr(&release, &mut ctx).is_ok(),
            "release through field wrapper must succeed"
        );
        assert!(!ctx.is_locked("account"), "release must clear the lock");
        assert!(!ctx.is_consumed("account"), "release must not consume the linear");
    }

    /// F5 — commit_transfer destructures `Locked<T>` and yields the committed
    /// value `T` (NOT the `Locked<T>` wrapper). WHY: returning the locked
    /// wrapper would type the commit result as still-locked, permitting a
    /// second elimination of the same resource.
    #[test]
    fn f5_commit_transfer_returns_unwrapped_value_type() {
        let ctx = TypeContext::new();
        // Inline lock produces `Locked<Linear<String>>`; commit must unwrap to
        // the committed value `String`.
        let commit = OpExpr::CommitTransfer {
            locked: Box::new(OpExpr::Lock {
                resource: Box::new(OpExpr::String("s".to_string())),
                corridor_id: "c".to_string(),
            }),
            witness: Box::new(OpExpr::Unit),
        };
        let ty = static_expr_type(&commit, &ctx).unwrap();
        assert_eq!(
            ty,
            OpType::String,
            "commit_transfer must yield the unwrapped committed value type, got {ty:?}"
        );
    }

    /// F5 — release_lock destructures `Locked<Linear<T>>` back to the
    /// unconsumed `Linear<T>`. WHY: a released resource must remain visibly
    /// linear so downstream double-use is still caught.
    #[test]
    fn f5_release_lock_returns_linear_type() {
        let ctx = TypeContext::new();
        let release = OpExpr::ReleaseLock {
            locked: Box::new(OpExpr::Lock {
                resource: Box::new(OpExpr::String("s".to_string())),
                corridor_id: "c".to_string(),
            }),
            witness: Box::new(OpExpr::Unit),
        };
        let ty = static_expr_type(&release, &ctx).unwrap();
        assert_eq!(
            ty,
            OpType::Linear(Box::new(OpType::String)),
            "release_lock must yield Linear<T>, got {ty:?}"
        );
    }

    /// F6 — after release_lock, the lock capability is spent; re-locking the
    /// same resource must be rejected. WHY: lock/release/lock/commit would let
    /// one linear resource be transferred across two corridors.
    #[test]
    fn f6_relock_after_release_is_rejected() {
        let mut ctx = linear_ctx("share");
        let lock = || OpExpr::Lock {
            resource: Box::new(OpExpr::Var("share".to_string())),
            corridor_id: "corr-a".to_string(),
        };
        assert!(check_expr(&lock(), &mut ctx).is_ok());
        let release = OpExpr::ReleaseLock {
            locked: Box::new(OpExpr::Var("share".to_string())),
            witness: Box::new(OpExpr::Unit),
        };
        assert!(check_expr(&release, &mut ctx).is_ok());
        assert!(!ctx.is_consumed("share"), "release does not consume");
        // Re-lock must now be rejected.
        let err = check_expr(&lock(), &mut ctx).unwrap_err();
        assert!(
            err.contains("lock-after-release"),
            "re-locking a released resource must be rejected, got: {err}"
        );
    }

    /// F6 — after commit_transfer, the resource is both consumed and its lock
    /// capability spent; re-locking is rejected (use-after-consume / spent).
    #[test]
    fn f6_relock_after_commit_is_rejected() {
        let mut ctx = linear_ctx("share");
        let lock = OpExpr::Lock {
            resource: Box::new(OpExpr::Var("share".to_string())),
            corridor_id: "corr-a".to_string(),
        };
        assert!(check_expr(&lock, &mut ctx).is_ok());
        let commit = OpExpr::CommitTransfer {
            locked: Box::new(OpExpr::Var("share".to_string())),
            witness: Box::new(OpExpr::Unit),
        };
        assert!(check_expr(&commit, &mut ctx).is_ok());
        let relock = OpExpr::Lock {
            resource: Box::new(OpExpr::Var("share".to_string())),
            corridor_id: "corr-b".to_string(),
        };
        assert!(
            check_expr(&relock, &mut ctx).is_err(),
            "re-locking a committed resource must be rejected"
        );
    }

    /// F6 — double-lock (locking an already-locked resource without
    /// release/commit) is rejected.
    #[test]
    fn f6_double_lock_is_rejected() {
        let mut ctx = linear_ctx("share");
        let lock = || OpExpr::Lock {
            resource: Box::new(OpExpr::Var("share".to_string())),
            corridor_id: "corr-a".to_string(),
        };
        assert!(check_expr(&lock(), &mut ctx).is_ok());
        let err = check_expr(&lock(), &mut ctx).unwrap_err();
        assert!(
            err.contains("double-lock"),
            "double-lock must be rejected, got: {err}"
        );
    }

    /// F7 — asymmetric consumption obligations are surfaced in the result. WHY:
    /// `branch_asymmetric_consumptions` was tracked but never returned, so a
    /// caller could not see which linear resources were consumed on only some
    /// branches.
    #[test]
    fn f7_asymmetric_consumption_is_surfaced_in_result() {
        let prog = trivial_program(vec![
            Statement::Let {
                name: "share".to_string(),
                ty: OpType::Linear(Box::new(OpType::String)),
                value: OpExpr::String("s".to_string()),
            },
            Statement::Choose {
                arms: vec![(
                    OpExpr::Bool(true),
                    vec![Statement::Expr(OpExpr::ConsumeLinear(Box::new(
                        OpExpr::Var("share".to_string()),
                    )))],
                )],
                else_block: Some(vec![Statement::Expr(OpExpr::Unit)]),
            },
        ]);
        let res = typecheck_program(&prog);
        assert!(
            res.asymmetric_consumption_obligations
                .contains(&"share".to_string()),
            "asymmetric consumption of `share` must be surfaced, got {:?}",
            res.asymmetric_consumption_obligations
        );
    }

    /// F8 — an encoded variant record `{tag, value}` must NOT type as an empty
    /// variant; a match on it must enforce exhaustiveness over the real
    /// constructor. WHY: an empty constructor list made every match vacuously
    /// exhaustive, defeating coverage checking.
    #[test]
    fn f8_encoded_variant_record_populates_constructor() {
        let ctx = TypeContext::new();
        let encoded = OpExpr::Record(vec![
            ("tag".to_string(), OpExpr::String("Approved".to_string())),
            ("value".to_string(), OpExpr::Int(7)),
        ]);
        let ty = static_expr_type(&encoded, &ctx).unwrap();
        assert_eq!(
            ty,
            OpType::Variant(vec![("Approved".to_string(), OpType::Int)]),
            "encoded variant record must carry its real constructor, got {ty:?}"
        );
        // A match missing the `Approved` arm must now be rejected (was
        // vacuously accepted under the empty-variant typing).
        let m = OpExpr::Match {
            scrutinee: Box::new(encoded),
            arms: vec![],
            catch_all: Box::new(OpExpr::Unit),
        };
        let err = static_expr_type(&m, &ctx).unwrap_err();
        assert!(
            err.contains("missing constructor arm `Approved`"),
            "match on encoded variant must require its constructor, got: {err}"
        );
    }

    // --- Variant match-arm JOIN (least-upper-bound) ---------------------------
    //
    // A defeasible Lex rule with exceptions lowers to a match whose arms are
    // DIFFERENT constructors of the same `Verdict` datatype. The match result
    // type must be the constructor-set UNION (the join in the variant subtyping
    // lattice), not a structural-equality demand on the two arms. The union is
    // a sound supertype of each arm (widening a singleton variant to a union
    // over the same datatype is sound); a tag reused with conflicting payloads
    // is a hard error (no silent coercion). WHY: without this, no defeasible
    // rule with exceptions can ever compile (a core Lex->Op incompleteness).

    /// An encoded `{tag, value}` verdict literal, mirroring the lowering's wire
    /// shape, so these tests exercise the real `static_expr_type` path.
    fn encoded_verdict(tag: &str, value: OpExpr) -> OpExpr {
        OpExpr::Record(vec![
            ("tag".to_string(), OpExpr::String(tag.to_string())),
            ("value".to_string(), value),
        ])
    }

    /// JOIN of two single-constructor variant arms is their constructor-set
    /// union, sorted by tag (deterministic). This is the `NonCompliant` over
    /// `Compliant` defeasible shape.
    #[test]
    fn variant_match_two_constructors_join_to_union() {
        let ctx = TypeContext::new();
        // match guard { true -> NonCompliant{reason}; false -> Compliant{} }
        // catch-all is itself a NonCompliant (the fail-closed value), so the
        // three arm types are {NonCompliant, Compliant, NonCompliant}.
        let m = OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![
                MatchArm {
                    pattern: "true".to_string(),
                    binding: "_".to_string(),
                    body: encoded_verdict(
                        "NonCompliant",
                        OpExpr::Record(vec![(
                            "reason".to_string(),
                            OpExpr::String("x".to_string()),
                        )]),
                    ),
                },
                MatchArm {
                    pattern: "false".to_string(),
                    binding: "_".to_string(),
                    body: encoded_verdict("Compliant", OpExpr::Unit),
                },
            ],
            catch_all: Box::new(encoded_verdict(
                "NonCompliant",
                OpExpr::Record(vec![(
                    "reason".to_string(),
                    OpExpr::String("unmatched".to_string()),
                )]),
            )),
        };
        let ty = static_expr_type(&m, &ctx).expect("variant arms must join");
        assert_eq!(
            ty,
            OpType::Variant(vec![
                ("Compliant".to_string(), OpType::Unit),
                (
                    "NonCompliant".to_string(),
                    OpType::Record(vec![("reason".to_string(), OpType::String)])
                ),
            ]),
            "join must be the tag-sorted constructor union, got {ty:?}"
        );
        // The join is a supertype of each arm: a program declaring the full
        // union as its output must accept this match body.
        assert!(matches!(
            check_expr(&m, &mut ctx.clone()),
            Ok(())
        ));
    }

    /// 3+ distinct constructors join to the full union. Built by nesting: the
    /// outer `false` arm is itself a match over two further constructors. This
    /// also exercises nested-match join propagation.
    #[test]
    fn variant_match_three_plus_constructors_and_nested() {
        let ctx = TypeContext::new();
        let inner = OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![
                MatchArm {
                    pattern: "true".to_string(),
                    binding: "_".to_string(),
                    body: encoded_verdict("Compliant", OpExpr::Unit),
                },
                MatchArm {
                    pattern: "false".to_string(),
                    binding: "_".to_string(),
                    body: encoded_verdict("Pending", OpExpr::Unit),
                },
            ],
            catch_all: Box::new(encoded_verdict("Compliant", OpExpr::Unit)),
        };
        // inner joins to {Compliant, Pending}
        let inner_ty = static_expr_type(&inner, &ctx).unwrap();
        assert_eq!(
            inner_ty,
            OpType::Variant(vec![
                ("Compliant".to_string(), OpType::Unit),
                ("Pending".to_string(), OpType::Unit),
            ])
        );
        let outer = OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![
                MatchArm {
                    pattern: "true".to_string(),
                    binding: "_".to_string(),
                    body: encoded_verdict("SanctionsBlocked", OpExpr::Unit),
                },
                MatchArm {
                    pattern: "false".to_string(),
                    binding: "_".to_string(),
                    body: inner,
                },
            ],
            catch_all: Box::new(encoded_verdict("SanctionsBlocked", OpExpr::Unit)),
        };
        let ty = static_expr_type(&outer, &ctx).expect("nested variant arms must join");
        assert_eq!(
            ty,
            OpType::Variant(vec![
                ("Compliant".to_string(), OpType::Unit),
                ("Pending".to_string(), OpType::Unit),
                ("SanctionsBlocked".to_string(), OpType::Unit),
            ]),
            "nested match joins to the full 3-constructor union, got {ty:?}"
        );
    }

    /// SOUNDNESS: a constructor tag reused across arms with CONFLICTING payload
    /// types is a hard TypeError — never silently merged or coerced. WHY:
    /// widening a singleton to a union is sound only when shared tags agree;
    /// `C(Int)` and `C(String)` are not the same constructor.
    #[test]
    fn variant_match_conflicting_payload_same_tag_is_type_error() {
        let ctx = TypeContext::new();
        let m = OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![
                MatchArm {
                    pattern: "true".to_string(),
                    binding: "_".to_string(),
                    body: encoded_verdict("C", OpExpr::Int(1)),
                },
                MatchArm {
                    pattern: "false".to_string(),
                    binding: "_".to_string(),
                    body: encoded_verdict("C", OpExpr::String("s".to_string())),
                },
            ],
            catch_all: Box::new(encoded_verdict("C", OpExpr::Int(0))),
        };
        let err = static_expr_type(&m, &ctx).unwrap_err();
        assert!(
            err.contains("conflicting payload types to constructor `C`"),
            "payload conflict on a shared tag must be a type error, got: {err}"
        );
        // It must also fail `check_expr` (the validation entry point), not just
        // the synthesis path.
        assert!(check_expr(&m, &mut ctx.clone()).is_err());
    }

    /// The join falls back to structural equality for NON-variant arms: a `Bool`
    /// arm next to an `Int` arm is still rejected exactly as before (the union
    /// rule only fires when every arm is a variant). WHY: the join must not
    /// loosen type checking for ordinary scalar/record arms.
    #[test]
    fn non_variant_arms_still_require_structural_equality() {
        let ctx = TypeContext::new();
        let m = OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![
                MatchArm {
                    pattern: "true".to_string(),
                    binding: "_".to_string(),
                    body: OpExpr::Int(1),
                },
                MatchArm {
                    pattern: "false".to_string(),
                    binding: "_".to_string(),
                    body: OpExpr::Bool(false),
                },
            ],
            catch_all: Box::new(OpExpr::Int(0)),
        };
        let err = static_expr_type(&m, &ctx).unwrap_err();
        assert!(
            err.contains("match arm `false` has type Bool"),
            "non-variant arm disagreement must still be rejected, got: {err}"
        );
    }

    /// A variant arm mixed with a non-variant arm is a genuine error (the union
    /// path requires ALL arms to be variants; a mix falls to structural
    /// equality, which they fail). WHY: widening a non-variant into a variant
    /// union is unsound and must be rejected.
    #[test]
    fn variant_mixed_with_non_variant_arm_is_rejected() {
        let ctx = TypeContext::new();
        let m = OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![
                MatchArm {
                    pattern: "true".to_string(),
                    binding: "_".to_string(),
                    body: encoded_verdict("Compliant", OpExpr::Unit),
                },
                MatchArm {
                    pattern: "false".to_string(),
                    binding: "_".to_string(),
                    body: OpExpr::Int(7),
                },
            ],
            catch_all: Box::new(encoded_verdict("Compliant", OpExpr::Unit)),
        };
        assert!(
            static_expr_type(&m, &ctx).is_err(),
            "a variant arm mixed with a non-variant arm must be rejected"
        );
    }

    /// Direct unit coverage of the join helper: union, conflict, non-variant
    /// fallback, and idempotent self-join.
    #[test]
    fn join_helper_unit_cases() {
        // union of two singletons (input order reversed → still tag-sorted)
        let joined = join_variant_arm_types(&[
            OpType::Variant(vec![("B".to_string(), OpType::Unit)]),
            OpType::Variant(vec![("A".to_string(), OpType::Int)]),
        ])
        .unwrap();
        assert_eq!(
            joined,
            Some(OpType::Variant(vec![
                ("A".to_string(), OpType::Int),
                ("B".to_string(), OpType::Unit),
            ])),
            "union must be tag-sorted regardless of input order"
        );
        // conflict on shared tag
        assert!(join_variant_arm_types(&[
            OpType::Variant(vec![("A".to_string(), OpType::Int)]),
            OpType::Variant(vec![("A".to_string(), OpType::Bool)]),
        ])
        .is_err());
        // non-variant present → None (caller applies structural equality)
        assert_eq!(
            join_variant_arm_types(&[OpType::Int, OpType::Variant(vec![])]).unwrap(),
            None
        );
        // self-join is idempotent (already-unioned type widens to itself)
        let v = OpType::Variant(vec![
            ("A".to_string(), OpType::Unit),
            ("B".to_string(), OpType::Unit),
        ]);
        assert_eq!(
            join_variant_arm_types(&[v.clone(), v.clone()]).unwrap(),
            Some(v)
        );
    }

    /// End-to-end: a program whose body is the defeasible match and whose
    /// declared output is the full union type type-checks (the join is a
    /// subtype of / equal to the declared union). WHY: this is the exact
    /// `build_program` -> `typecheck_program` contract the compiler relies on.
    #[test]
    fn declared_union_output_accepts_defeasible_match_body() {
        let body = OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![
                MatchArm {
                    pattern: "true".to_string(),
                    binding: "_".to_string(),
                    body: encoded_verdict(
                        "NonCompliant",
                        OpExpr::Record(vec![(
                            "reason".to_string(),
                            OpExpr::String("r".to_string()),
                        )]),
                    ),
                },
                MatchArm {
                    pattern: "false".to_string(),
                    binding: "_".to_string(),
                    body: encoded_verdict("Compliant", OpExpr::Unit),
                },
            ],
            catch_all: Box::new(encoded_verdict(
                "NonCompliant",
                OpExpr::Record(vec![(
                    "reason".to_string(),
                    OpExpr::String("unmatched".to_string()),
                )]),
            )),
        };
        let mut prog = trivial_program(vec![Statement::Return(body)]);
        prog.outputs = vec![(
            "result".to_string(),
            OpType::Variant(vec![
                ("Compliant".to_string(), OpType::Unit),
                (
                    "NonCompliant".to_string(),
                    OpType::Record(vec![("reason".to_string(), OpType::String)]),
                ),
            ]),
        )];
        let res = typecheck_program(&prog);
        assert!(
            res.success,
            "declared union output must accept the defeasible match body: {:?}",
            res.errors
        );
    }

    /// F9 — an unknown primitive call used in a type-inference position is
    /// rejected, not silently typed as an empty record. WHY: silent empty-record
    /// typing let any downstream type flow through unchecked.
    #[test]
    fn f9_unknown_primitive_call_inference_is_rejected() {
        let ctx = TypeContext::new();
        let call = OpExpr::Call("unknown.primitive".to_string(), vec![]);
        let err = static_expr_type(&call, &ctx).unwrap_err();
        assert!(
            err.contains("unknown primitive call"),
            "unknown primitive call must fail inference, got: {err}"
        );
    }

    /// F9 — the `run` placeholder-binding path is preserved (a `run name = prim()`
    /// binds the host-determined record placeholder and does NOT route through
    /// the `static_expr_type(Call)` inference that F9 now fails loud on). Uses a
    /// recognized primitive so the orthogonal effect-row check (which rejects
    /// primitives with no canonical effects) is satisfied. WHY: F9 must reject
    /// the inference position WITHOUT breaking the legitimate `run` binding.
    #[test]
    fn f9_run_binding_placeholder_path_is_preserved() {
        let mut prog = trivial_program(vec![
            Statement::Run {
                name: "r".to_string(),
                call: OpExpr::Call("attestation.append".to_string(), vec![]),
            },
            Statement::Return(OpExpr::Var("r".to_string())),
        ]);
        prog.effects = vec![Effect::ProofEmit];
        let res = typecheck_program(&prog);
        assert!(
            res.success,
            "run-bound recognized primitive must typecheck (placeholder path): {:?}",
            res.errors
        );
    }

    /// F10 — an extensional gas bound that overflows u64 is rejected (was
    /// silently saturated to u64::MAX). WHY: a saturated cap is a fabricated,
    /// valid-looking bound for a program whose true cost is unrepresentable.
    #[test]
    fn f10_extensional_gas_overflow_is_rejected() {
        let mut prog = trivial_program(vec![]);
        prog.gas_budget = GasBudget {
            structural_gas: 0,
            per_element_gas: u64::MAX,
            cardinality_certificate: Some(CardinalityCertificate {
                query: "q".to_string(),
                cardinality: 2,
                as_of: "2026-01-01T00:00:00Z".to_string(),
                signature: "sig".to_string(),
            }),
        };
        let res = typecheck_program(&prog);
        assert!(!res.success, "overflowing extensional bound must be rejected");
        assert!(
            res.errors
                .iter()
                .any(|e| e.contains("extensional gas bound overflows u64")),
            "overflow must be surfaced, got {:?}",
            res.errors
        );
    }

    /// F10 — a representable extensional bound is computed exactly (no spurious
    /// rejection, and the value is the true product).
    #[test]
    fn f10_representable_extensional_bound_is_exact() {
        let mut prog = trivial_program(vec![]);
        prog.gas_budget = GasBudget {
            structural_gas: 0,
            per_element_gas: 10,
            cardinality_certificate: Some(CardinalityCertificate {
                query: "q".to_string(),
                cardinality: 4300,
                as_of: "2026-01-01T00:00:00Z".to_string(),
                signature: "sig".to_string(),
            }),
        };
        let res = typecheck_program(&prog);
        assert!(res.success, "representable bound: {:?}", res.errors);
        assert_eq!(
            res.gas_analysis.unwrap().max_extensional_gas,
            Some(43_000)
        );
    }

    /// F11 — `AssertSafety` buried inside a match arm body is still fail-loud
    /// (no silent-accept path through nested expressions). WHY: a bare safety
    /// predicate with no verified receipt must never be accepted, regardless of
    /// nesting.
    #[test]
    fn f11_nested_assert_safety_fails_loud() {
        let prog = trivial_program(vec![Statement::Expr(OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![
                MatchArm {
                    pattern: "true".to_string(),
                    binding: "_".to_string(),
                    body: OpExpr::AssertSafety(SafetyPredicate::NoGroupFormationBypass),
                },
                MatchArm {
                    pattern: "false".to_string(),
                    binding: "_".to_string(),
                    body: OpExpr::Unit,
                },
            ],
            catch_all: Box::new(OpExpr::Unit),
        })]);
        let res = typecheck_program(&prog);
        assert!(!res.success, "nested bare AssertSafety must fail");
        assert!(
            res.errors
                .iter()
                .any(|e| e.contains("requires a verified receipt")),
            "nested AssertSafety must surface the receipt error, got {:?}",
            res.errors
        );
    }

    /// F11 — a `policy` block with no verified proof receipt is rejected (the
    /// gate is not vacuous).
    #[test]
    fn f11_policy_block_requires_receipt() {
        let prog = trivial_program(vec![Statement::Policy {
            name: "kyc".to_string(),
            domains: vec!["Kyc".to_string()],
        }]);
        let res = typecheck_program(&prog);
        assert!(!res.success, "policy block must require a receipt");
        assert!(res
            .errors
            .iter()
            .any(|e| e.contains("requires a verified proof receipt")));
    }

    /// F-MEDIUM (initializer asymmetry) — a `let x: T = <Linear<T> initializer>`
    /// binds the linear type so x stays single-use and downstream double-use is
    /// caught. WHY: binding the bare annotation would erase the linearity and
    /// silently permit reuse.
    #[test]
    fn f_medium_let_preserves_linearity_from_initializer() {
        // value `lock(...)`-less: use a Var bound Linear, re-bound via let with
        // a bare annotation. Build a program: outer linear `src`, then
        // `let aliased: String = src` (annotation bare String, initializer
        // Linear<String>) — the binding must remain Linear<String> so consuming
        // `aliased` twice is rejected.
        let prog = trivial_program(vec![
            Statement::Let {
                name: "src".to_string(),
                ty: OpType::Linear(Box::new(OpType::String)),
                value: OpExpr::String("s".to_string()),
            },
            Statement::Let {
                name: "aliased".to_string(),
                ty: OpType::String,
                value: OpExpr::Var("src".to_string()),
            },
            Statement::Expr(OpExpr::ConsumeLinear(Box::new(OpExpr::Var(
                "aliased".to_string(),
            )))),
            Statement::Expr(OpExpr::ConsumeLinear(Box::new(OpExpr::Var(
                "aliased".to_string(),
            )))),
        ]);
        let res = typecheck_program(&prog);
        assert!(
            !res.success,
            "double-consume of a linearly-initialized binding must be rejected"
        );
        assert!(
            res.linearity_violations.contains(&"aliased".to_string()),
            "the re-bound name must remain linear and surface a violation, got {:?}",
            res.linearity_violations
        );
    }

    /// F-MEDIUM (structural gas) — a structural gas bound exceeding the declared
    /// budget is surfaced as an error. WHY: a declared budget that the skeleton
    /// provably overruns is a budget violation the checker must not ignore.
    #[test]
    fn f_medium_structural_gas_over_budget_is_surfaced() {
        // A program with a non-trivial body costs > 0 structurally. Declare an
        // impossibly tight budget of 1 and confirm the overrun is surfaced.
        let prog_unbudgeted = {
            let mut p = trivial_program(vec![
                Statement::Expr(OpExpr::Unit),
                Statement::Return(OpExpr::Unit),
            ]);
            p.gas_budget = GasBudget::default();
            p
        };
        let baseline = typecheck_program(&prog_unbudgeted);
        let structural = baseline.gas_analysis.unwrap().structural_bound;
        // Only meaningful if the skeleton has positive structural cost.
        if structural > 0 {
            let mut prog = trivial_program(vec![
                Statement::Expr(OpExpr::Unit),
                Statement::Return(OpExpr::Unit),
            ]);
            prog.gas_budget = GasBudget {
                structural_gas: 1,
                per_element_gas: 0,
                cardinality_certificate: None,
            };
            let res = typecheck_program(&prog);
            assert!(
                res.errors
                    .iter()
                    .any(|e| e.contains("structural gas bound") && e.contains("exceeds declared budget")),
                "over-budget structural gas must be surfaced, got {:?}",
                res.errors
            );
        }
    }
}
