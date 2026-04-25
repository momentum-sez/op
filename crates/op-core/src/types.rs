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
            if !all_consumed.contains(name) && !self.branch_asymmetric_consumptions.contains(name) {
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
    let extensional_bound = program
        .gas_budget
        .cardinality_certificate
        .as_ref()
        .map(|c| {
            program
                .gas_budget
                .per_element_gas
                .saturating_mul(c.cardinality)
        });

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
        failed_predicates: failed,
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
    annotation == actual || matches!(annotation, OpType::Linear(inner) if inner.as_ref() == actual)
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
            match static_expr_type(value, ctx) {
                Ok(actual) if initializer_compatible(ty, &actual) => {}
                Ok(actual) => errors.push(format!(
                    "let `{name}` initializer type {actual:?} does not match annotation {ty:?}"
                )),
                Err(err) => errors.push(format!("in let {name} type inference: {err}")),
            }
            ctx.bind(name.clone(), ty.clone());
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
            let mut result_ty: Option<OpType> = None;
            for arm in arms {
                let mut sub = ctx.clone();
                if !arm.binding.is_empty() && arm.binding != "_" {
                    sub.bind(
                        arm.binding.clone(),
                        match_binding_type(&scrutinee_ty, &arm.pattern)?,
                    );
                }
                check_expr(&arm.body, &mut sub)?;
                let arm_ty = static_expr_type(&arm.body, &sub)?;
                if let Some(expected) = &result_ty {
                    if expected != &arm_ty {
                        return Err(format!(
                            "match arm `{}` has type {:?}, expected {:?}",
                            arm.pattern, arm_ty, expected
                        ));
                    }
                } else {
                    result_ty = Some(arm_ty);
                }
            }
            check_expr(catch_all, ctx)?;
            let catch_ty = static_expr_type(catch_all, ctx)?;
            if let Some(expected) = &result_ty {
                if expected != &catch_ty {
                    return Err(format!(
                        "match catch-all has type {catch_ty:?}, expected {expected:?}"
                    ));
                }
            }
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
        OpExpr::Record(fields) => fields
            .iter()
            .map(|(name, value)| Ok((name.clone(), static_expr_type(value, ctx)?)))
            .collect::<Result<Vec<_>, _>>()
            .map(|field_types| {
                if is_encoded_variant_record(fields) {
                    OpType::Variant(vec![])
                } else {
                    OpType::Record(field_types)
                }
            }),
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
        OpExpr::Call(name, _) => Ok(match name.as_str() {
            "sanctions.check" => op_verdict_variant(),
            "attestation.append" => OpType::Record(vec![]),
            _ => OpType::Record(vec![]),
        }),
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
            let mut result_ty: Option<OpType> = None;
            for arm in arms {
                let mut sub = ctx.clone();
                if !arm.binding.is_empty() && arm.binding != "_" {
                    sub.bind(
                        arm.binding.clone(),
                        match_binding_type(&scrutinee_ty, &arm.pattern)?,
                    );
                }
                let ty = static_expr_type(&arm.body, &sub)?;
                if let Some(expected) = &result_ty {
                    if expected != &ty {
                        return Err(format!(
                            "match arm `{}` has type {:?}, expected {:?}",
                            arm.pattern, ty, expected
                        ));
                    }
                } else {
                    result_ty = Some(ty);
                }
            }
            let catch_ty = static_expr_type(catch_all, ctx)?;
            if let Some(expected) = &result_ty {
                if expected != &catch_ty {
                    return Err(format!(
                        "match catch-all has type {catch_ty:?}, expected {expected:?}"
                    ));
                }
                Ok(expected.clone())
            } else {
                Ok(catch_ty)
            }
        }
        OpExpr::AssertSafety(_) => Ok(OpType::Unit),
        OpExpr::ConsumeLinear(inner) => static_expr_type(inner, ctx),
        OpExpr::Lock { resource, .. } => {
            Ok(OpType::Locked(Box::new(static_expr_type(resource, ctx)?)))
        }
        OpExpr::CommitTransfer { locked, .. } | OpExpr::ReleaseLock { locked, .. } => {
            static_expr_type(locked, ctx)
        }
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
}
