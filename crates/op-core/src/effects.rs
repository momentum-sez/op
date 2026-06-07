//! Effect rows and effect-safety analysis.
//!
//! Op effects compose by union. Some effect pairs impose ordering constraints
//! that the compiler enforces — in particular, any reachable `sovereign_write`,
//! `identity_mutation`, or `fiscal_transfer` must be dominated by a
//! `sanctions_check`, with a single deferred-subject exception: entity
//! creation where the subject does not yet exist.
//!
//! The analysis walks every reachable position — statement-level step
//! signatures AND expression-level host calls surfaced inside `Return`,
//! `Expr`, `Run`, `Let` bodies. The expression walker consults a built-in
//! primitive-effects table mirroring the canonical corpus, so that a bare
//! `OpExpr::Call("ownership.transfer", ...)` is rejected at the same
//! precedence as a `Statement::Step` declaring `SovereignWrite`.

use crate::ast::{Effect, MatchArm, OpExpr, OpProgram, Statement, StepBody};
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

    /// An expression-level host call names no canonical primitive. Unknown
    /// primitives are not pure by default; embedders must route them through a
    /// typed step signature or a future signed primitive registry.
    #[error("unknown primitive '{primitive}' at '{site}' has no canonical effect row")]
    UnknownPrimitive {
        /// Primitive identifier.
        primitive: String,
        /// Statement or step site.
        site: String,
    },

    /// A primitive step declared an effect not present in its canonical row.
    /// Caller-provided signatures are not evidence for host effects.
    #[error(
        "step '{step}' declares {effect:?} for primitive '{primitive}', but the canonical row does \
         not justify it"
    )]
    UnjustifiedStepEffect {
        /// Step identifier.
        step: String,
        /// Primitive identifier.
        primitive: String,
        /// Unjustified declared effect.
        effect: Effect,
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
///
/// Expression-level host calls surfaced inside `Return`, `Expr`, `Run`,
/// and `Let` bodies are walked by [`walk_expr_effects`], which consults the
/// canonical primitive-effects table and rejects any write-class effect
/// without a dominating sanctions check under the same precedence as
/// statement-level step signatures.
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
                // Update sanctions visibility only from effects justified by
                // the step body itself. A caller-provided signature cannot
                // certify its own dominator.
                if step_authoritative_effects(step)
                    .iter()
                    .any(|e| *e == Effect::SanctionsCheck)
                {
                    self.sanctions_seen = true;
                }
            }
            Statement::Let { name, value, .. } => {
                self.check_expr_in_stmt(value, name);
            }
            Statement::Return(expr) | Statement::Expr(expr) => {
                self.check_expr_in_stmt(expr, "<expr>");
            }
            Statement::Run { name, call } => {
                self.check_expr_in_stmt(call, name);
            }
            Statement::Par { branches } => {
                // Each branch observes the current environment but cannot see siblings.
                let parent_sanctions = self.sanctions_seen;
                let mut all_sanctions_after = true;
                for (name, expr) in branches {
                    let mut sub = SafetyCtx {
                        sanctions_seen: parent_sanctions,
                        errors: Vec::new(),
                    };
                    sub.check_expr_in_stmt(expr, name);
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
                for (guard, branch) in arms {
                    // The guard is evaluated in the pre-branch environment;
                    // writes inside it are bound by the outer dominator state.
                    self.check_expr_in_stmt(guard, "<guard>");
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

    /// Walk an expression inside a statement context, checking every call's
    /// inferred effect row against the sanctions dominator. Updates
    /// `sanctions_seen` if the expression carries a `SanctionsCheck` effect
    /// (e.g. a `sanctions.check` call).
    fn check_expr_in_stmt(&mut self, expr: &OpExpr, site: &str) {
        if let OpExpr::Seq(a, b) = expr {
            self.check_expr_in_stmt(a, site);
            self.check_expr_in_stmt(b, site);
            return;
        }

        for primitive in unknown_expr_calls(expr) {
            self.errors.push(EffectSafetyError::UnknownPrimitive {
                primitive,
                site: site.to_string(),
            });
        }

        let walked = walk_expr_effects(expr);
        let write_class = write_class_effects();
        for entry in &walked {
            if write_class.contains(&entry.effect) && !self.sanctions_seen {
                // Deferred-subject exception: if the primitive being called
                // is entity-creation class, a post-flight sanctions check
                // is permitted.
                if !entry.deferred_subject {
                    self.errors.push(EffectSafetyError::UndominatedWrite {
                        effect: entry.effect.clone(),
                        step: format!("{site}:{}", entry.call_name),
                    });
                }
            }
        }
        if walked.iter().any(|e| e.effect == Effect::SanctionsCheck) {
            self.sanctions_seen = true;
        }
    }

    fn check_step(&mut self, step: &crate::ast::OpStep) {
        let write_class = write_class_effects();
        let authoritative_effects = step_authoritative_effects(step);
        let step_has_write = authoritative_effects
            .iter()
            .any(|e| write_class.contains(e));

        if step_has_write && !self.sanctions_seen {
            // Deferred-subject exception: if the step is an entity-creation
            // primitive, the sanctions check is allowed to run post-flight.
            if !is_entity_create_primitive(&step.body) {
                for e in &authoritative_effects {
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
            let has_compensable = authoritative_effects.iter().any(|e| {
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
            && authoritative_effects
                .iter()
                .any(|e| *e == Effect::SovereignWrite)
        {
            self.errors
                .push(EffectSafetyError::ContinueOnSovereignWrite {
                    step: step.id.clone(),
                });
        }

        if let Some(comp) = &step.compensate {
            self.check_compensation_body(&comp.body, &format!("{}:compensate", step.id));
        }

        // Arguments to a step's primitive body, and any inline block body,
        // carry their own expression-level effects that must equally respect
        // the dominator state. We track sanctions visibility updates within
        // the step's own expression positions because a well-formed step may
        // chain a sanctions sub-call before a subsequent write.
        match &step.body {
            StepBody::Primitive(prim, args) => {
                let canonical_known = canonical_primitive_known(&prim.0);
                if !canonical_known {
                    self.errors.push(EffectSafetyError::UnknownPrimitive {
                        primitive: prim.0.clone(),
                        site: step.id.clone(),
                    });
                } else {
                    let canonical: BTreeSet<_> =
                        canonical_effects_for(&prim.0).into_iter().collect();
                    for effect in &step.signature.effects {
                        if !matches!(effect, Effect::Pure) && !canonical.contains(effect) {
                            self.errors.push(EffectSafetyError::UnjustifiedStepEffect {
                                step: step.id.clone(),
                                primitive: prim.0.clone(),
                                effect: effect.clone(),
                            });
                        }
                    }
                }

                // Treat the call as a synthetic expression: primitive's
                // canonical effects + every argument's effects.
                let mut synthesized = Vec::new();
                for eff in canonical_effects_for(&prim.0) {
                    synthesized.push(WalkedCall {
                        call_name: prim.0.clone(),
                        effect: eff,
                        deferred_subject: canonical_is_deferred_subject(&prim.0),
                    });
                }
                for (_, arg) in args {
                    for primitive in unknown_expr_calls(arg) {
                        self.errors.push(EffectSafetyError::UnknownPrimitive {
                            primitive,
                            site: format!("{}:{}", step.id, prim.0),
                        });
                    }
                    synthesized.extend(walk_expr_effects(arg));
                }
                for entry in &synthesized {
                    if write_class.contains(&entry.effect)
                        && !self.sanctions_seen
                        && !entry.deferred_subject
                    {
                        // Step already reports this via the signature-level
                        // path; skip duplicates when the step declared the
                        // same effect on its signature.
                        if !step.signature.effects.contains(&entry.effect) {
                            self.errors.push(EffectSafetyError::UndominatedWrite {
                                effect: entry.effect.clone(),
                                step: format!("{}:{}", step.id, entry.call_name),
                            });
                        }
                    }
                }
                if synthesized
                    .iter()
                    .any(|e| e.effect == Effect::SanctionsCheck)
                {
                    self.sanctions_seen = true;
                }
            }
            StepBody::Block(inner) => {
                let parent = self.sanctions_seen;
                let mut sub = SafetyCtx {
                    sanctions_seen: parent,
                    errors: Vec::new(),
                };
                sub.walk_block(inner);
                self.errors.extend(sub.errors);
                self.sanctions_seen = self.sanctions_seen || sub.sanctions_seen;
            }
        }
    }

    fn check_compensation_body(&mut self, body: &StepBody, site: &str) {
        let write_class = write_class_effects();
        match body {
            StepBody::Primitive(prim, args) => {
                if !canonical_primitive_known(&prim.0) {
                    self.errors.push(EffectSafetyError::UnknownPrimitive {
                        primitive: prim.0.clone(),
                        site: site.to_string(),
                    });
                }

                let mut synthesized = Vec::new();
                for (_, arg) in args {
                    for primitive in unknown_expr_calls(arg) {
                        self.errors.push(EffectSafetyError::UnknownPrimitive {
                            primitive,
                            site: format!("{site}:{}", prim.0),
                        });
                    }
                    synthesized.extend(walk_expr_effects(arg));
                }
                for eff in canonical_effects_for(&prim.0) {
                    synthesized.push(WalkedCall {
                        call_name: prim.0.clone(),
                        effect: eff,
                        deferred_subject: false,
                    });
                }

                for entry in &synthesized {
                    if write_class.contains(&entry.effect) && !self.sanctions_seen {
                        self.errors.push(EffectSafetyError::UndominatedWrite {
                            effect: entry.effect.clone(),
                            step: format!("{site}:{}", entry.call_name),
                        });
                    }
                }
                if synthesized
                    .iter()
                    .any(|e| e.effect == Effect::SanctionsCheck)
                {
                    self.sanctions_seen = true;
                }
            }
            StepBody::Block(inner) => {
                let parent = self.sanctions_seen;
                let mut sub = SafetyCtx {
                    sanctions_seen: parent,
                    errors: Vec::new(),
                };
                sub.walk_block(inner);
                self.errors.extend(sub.errors);
                self.sanctions_seen = self.sanctions_seen || sub.sanctions_seen;
            }
        }
    }
}

/// One reachable call surfaced by the expression walker, with its inferred
/// effect and whether the callee is in the deferred-subject class.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WalkedCall {
    /// Dotted call name (e.g. `ownership.transfer`).
    pub(crate) call_name: String,
    /// One of the effects the callee carries.
    pub(crate) effect: Effect,
    /// Whether the callee qualifies for the deferred-subject exception.
    pub(crate) deferred_subject: bool,
}

/// Recursively infer the reachable call effects of an expression.
///
/// Every `OpExpr::Call(name, args)` contributes the canonical effect row of
/// `name` (looked up in the canonical primitive table) plus the effects of
/// its arguments. `Match`, `Seq`, `Record`, `BinOp`, and the linear / lock
/// eliminators recurse into their sub-expressions. Literals contribute
/// nothing.
pub(crate) fn walk_expr_effects(expr: &OpExpr) -> Vec<WalkedCall> {
    let mut out: Vec<WalkedCall> = Vec::new();
    walk_expr_effects_into(expr, &mut out);
    out
}

fn unknown_expr_calls(expr: &OpExpr) -> Vec<String> {
    let mut out = Vec::new();
    collect_unknown_expr_calls(expr, &mut out);
    out.sort();
    out.dedup();
    out
}

fn collect_unknown_expr_calls(expr: &OpExpr, out: &mut Vec<String>) {
    match expr {
        OpExpr::Unit
        | OpExpr::Bool(_)
        | OpExpr::Int(_)
        | OpExpr::String(_)
        | OpExpr::Null
        | OpExpr::Var(_)
        | OpExpr::Await { .. }
        | OpExpr::AssertSafety(_) => {}
        OpExpr::Field(e, _) => collect_unknown_expr_calls(e, out),
        OpExpr::Record(fields) => {
            for (_, e) in fields {
                collect_unknown_expr_calls(e, out);
            }
        }
        OpExpr::List(es) | OpExpr::Tuple(es) => {
            for e in es {
                collect_unknown_expr_calls(e, out);
            }
        }
        OpExpr::Call(name, args) => {
            if !canonical_primitive_known(name) {
                out.push(name.clone());
            }
            for (_, a) in args {
                collect_unknown_expr_calls(a, out);
            }
        }
        OpExpr::BinOp(_, a, b) | OpExpr::Coalesce(a, b) | OpExpr::Seq(a, b) => {
            collect_unknown_expr_calls(a, out);
            collect_unknown_expr_calls(b, out);
        }
        OpExpr::UnOp(_, a) => collect_unknown_expr_calls(a, out),
        OpExpr::Match {
            scrutinee,
            arms,
            catch_all,
        } => {
            collect_unknown_expr_calls(scrutinee, out);
            for MatchArm { body, .. } in arms {
                collect_unknown_expr_calls(body, out);
            }
            collect_unknown_expr_calls(catch_all, out);
        }
        OpExpr::ConsumeLinear(inner) => collect_unknown_expr_calls(inner, out),
        OpExpr::Lock { resource, .. } => collect_unknown_expr_calls(resource, out),
        OpExpr::CommitTransfer { locked, witness } | OpExpr::ReleaseLock { locked, witness } => {
            collect_unknown_expr_calls(locked, out);
            collect_unknown_expr_calls(witness, out);
        }
    }
}

fn walk_expr_effects_into(expr: &OpExpr, out: &mut Vec<WalkedCall>) {
    match expr {
        OpExpr::Unit
        | OpExpr::Bool(_)
        | OpExpr::Int(_)
        | OpExpr::String(_)
        | OpExpr::Null
        | OpExpr::Var(_)
        | OpExpr::Await { .. }
        | OpExpr::AssertSafety(_) => {}
        OpExpr::Field(e, _) => walk_expr_effects_into(e, out),
        OpExpr::Record(fields) => {
            for (_, e) in fields {
                walk_expr_effects_into(e, out);
            }
        }
        OpExpr::List(es) | OpExpr::Tuple(es) => {
            for e in es {
                walk_expr_effects_into(e, out);
            }
        }
        OpExpr::Call(name, args) => {
            for eff in canonical_effects_for(name) {
                out.push(WalkedCall {
                    call_name: name.clone(),
                    effect: eff,
                    deferred_subject: canonical_is_deferred_subject(name),
                });
            }
            for (_, a) in args {
                walk_expr_effects_into(a, out);
            }
        }
        OpExpr::BinOp(_, a, b) | OpExpr::Coalesce(a, b) | OpExpr::Seq(a, b) => {
            walk_expr_effects_into(a, out);
            walk_expr_effects_into(b, out);
        }
        OpExpr::UnOp(_, a) => walk_expr_effects_into(a, out),
        OpExpr::Match {
            scrutinee,
            arms,
            catch_all,
        } => {
            walk_expr_effects_into(scrutinee, out);
            for MatchArm { body, .. } in arms {
                walk_expr_effects_into(body, out);
            }
            walk_expr_effects_into(catch_all, out);
        }
        OpExpr::ConsumeLinear(inner) => walk_expr_effects_into(inner, out),
        OpExpr::Lock { resource, .. } => walk_expr_effects_into(resource, out),
        OpExpr::CommitTransfer { locked, witness } | OpExpr::ReleaseLock { locked, witness } => {
            walk_expr_effects_into(locked, out);
            walk_expr_effects_into(witness, out);
        }
    }
}

/// Canonical primitive effect table — the single source of truth for the
/// default effect row of every canonical primitive.
///
/// op-core cannot depend on op-stdlib (stdlib depends on core), so the shape
/// table lives here and op-stdlib's `CANONICAL_PRIMITIVES` derives its effect
/// rows from this function (see `op_stdlib::default_effects`). A primitive name
/// not present returns an empty effect row **for aggregation only**; this is not
/// a silent admission. Safety checking rejects unknown step/expression calls
/// explicitly (`EffectSafetyError::UnknownPrimitive`), so an unknown primitive
/// never passes the gate with an empty row — embedders must not rely on host
/// rejection as an effect proof. The
/// `op_stdlib::stdlib_effects_match_op_core` parity test pins op-stdlib's
/// corpus to this table across the full primitive set.
pub fn canonical_effects_for(name: &str) -> Vec<Effect> {
    match name {
        // Entity
        "create.entity" => vec![Effect::SovereignWrite],
        "update.entity_status" => vec![Effect::SovereignWrite],
        // Ownership
        "ownership.issue_shares" => vec![Effect::SovereignWrite],
        "ownership.transfer" => vec![Effect::SovereignWrite],
        "update.cap_table" => vec![Effect::SovereignWrite],
        "membership.admit" => vec![Effect::SovereignWrite],
        // Fiscal
        "create.treasury" => vec![Effect::SovereignWrite],
        "create.bank_account" => vec![Effect::SovereignWrite],
        "fiscal.open_account" => vec![Effect::SovereignWrite],
        "fiscal.transfer" => vec![Effect::FiscalTransfer, Effect::SovereignWrite],
        // Identity
        "identity.verify" => vec![Effect::ExternalRead, Effect::IdentityMutation],
        // Consent
        "consent.board_resolution" | "consent.member_resolution" | "consent.shareholder_vote" => {
            vec![Effect::GovernanceRequest, Effect::SovereignWrite]
        }
        // Screening
        "screening.sanctions" | "sanctions.check" => {
            vec![Effect::SanctionsCheck, Effect::ExternalRead]
        }
        // Trade
        "trade.invoice_create" | "trade.lc_issue" => {
            vec![Effect::FiscalTransfer, Effect::SovereignWrite]
        }
        // Document
        "document.board_minutes"
        | "document.shareholder_minutes"
        | "document.commercial_invoice" => {
            vec![Effect::DocumentGeneration]
        }
        // Filing
        "filing.registry_amendment" => {
            vec![Effect::SovereignWrite, Effect::ProofEmit]
        }
        // Attestation — ProofEmit only; successful append is tau-labelled.
        // Failed persistence is not tau and must fail closed.
        "attestation.append" | "attestation.emit" => vec![Effect::ProofEmit],
        _ => Vec::new(),
    }
}

pub(crate) fn canonical_primitive_known(name: &str) -> bool {
    matches!(
        name,
        "create.entity"
            | "update.entity_status"
            | "ownership.issue_shares"
            | "ownership.transfer"
            | "update.cap_table"
            | "membership.admit"
            | "create.treasury"
            | "create.bank_account"
            | "fiscal.open_account"
            | "fiscal.transfer"
            | "identity.verify"
            | "consent.board_resolution"
            | "consent.member_resolution"
            | "consent.shareholder_vote"
            | "screening.sanctions"
            | "sanctions.check"
            | "trade.invoice_create"
            | "trade.lc_issue"
            | "document.board_minutes"
            | "document.shareholder_minutes"
            | "document.commercial_invoice"
            | "filing.registry_amendment"
            | "attestation.append"
            | "attestation.emit"
    )
}

/// The single canonical predicate for the deferred-subject (entity-creation)
/// sanctions exception. This is the ONE source of truth consulted by both the
/// expression-level walker ([`walk_expr_effects_into`], `canonical_effects_for`
/// synthesis) and the statement-level [`SafetyCtx::check_step`] path, so the
/// unscreened-write exception is exactly the same primitive set at every
/// precedence. Mirrors `op_stdlib::is_deferred_subject` (which resolves through
/// the `CANONICAL_PRIMITIVES` table); the spec lists `create.entity` as the
/// only canonical deferred-subject primitive.
///
/// Soundness note: a *broader* match here than at the other level would let a
/// primitive be treated as entity-create at one precedence but not the other,
/// so a deferred (unscreened) subject could slip the sanctions/subject
/// discipline at the level with the looser predicate. Both levels MUST consult
/// this function. The `levels_agree_on_deferred_subject_set` test pins the
/// agreement across the full canonical primitive set.
///
/// This is also the single source of truth for op-stdlib's `deferred_subject`
/// column: `op_stdlib::is_deferred_subject` resolves through this function, and
/// the `op_stdlib::stdlib_deferred_subject_matches_op_core` parity test binds
/// the two so the sanctions-domination exemption set cannot drift across the
/// crate boundary. The exemption set MUST stay exactly `{create.entity}`.
pub fn canonical_is_deferred_subject(name: &str) -> bool {
    matches!(name, "create.entity")
}

/// Statement-level adapter over [`canonical_is_deferred_subject`]. Identifies
/// whether a step body invokes the deferred-subject entity-creation primitive.
/// Delegates to the single canonical predicate so the statement-level exception
/// set is byte-for-byte the expression-level set (no prefix widening).
fn is_entity_create_primitive(body: &StepBody) -> bool {
    match body {
        StepBody::Primitive(p, _) => canonical_is_deferred_subject(&p.0),
        StepBody::Block(_) => false,
    }
}

fn step_authoritative_effects(step: &crate::ast::OpStep) -> BTreeSet<Effect> {
    let mut effects = BTreeSet::new();
    match &step.body {
        StepBody::Primitive(prim, _args) => {
            for effect in canonical_effects_for(&prim.0) {
                effects.insert(effect);
            }
        }
        StepBody::Block(_inner) => {
            for effect in &step.signature.effects {
                if !matches!(effect, Effect::Pure) {
                    effects.insert(effect.clone());
                }
            }
        }
    }
    effects
}

/// Flatten all effects occurring in any expression (used when computing
/// program-level effect rows from a mixed body).
#[allow(dead_code)]
pub(crate) fn expr_effects(expr: &OpExpr) -> EffectRow {
    match expr {
        OpExpr::Await { event, .. } => EffectRow::singleton(Effect::Await(event.clone())),
        OpExpr::ConsumeLinear(inner)
        | OpExpr::Lock {
            resource: inner, ..
        } => expr_effects(inner),
        OpExpr::CommitTransfer { locked, witness } | OpExpr::ReleaseLock { locked, witness } => {
            expr_effects(locked).union(&expr_effects(witness))
        }
        OpExpr::Record(fields) => fields.iter().fold(EffectRow::empty(), |acc, (_, e)| {
            acc.union(&expr_effects(e))
        }),
        OpExpr::List(items) | OpExpr::Tuple(items) => items
            .iter()
            .fold(EffectRow::empty(), |acc, e| acc.union(&expr_effects(e))),
        OpExpr::Call(name, args) => {
            let mut row = EffectRow::from(canonical_effects_for(name));
            for (_, e) in args {
                row = row.union(&expr_effects(e));
            }
            row
        }
        OpExpr::BinOp(_, a, b) => expr_effects(a).union(&expr_effects(b)),
        OpExpr::UnOp(_, a) => expr_effects(a),
        OpExpr::Coalesce(a, b) => expr_effects(a).union(&expr_effects(b)),
        OpExpr::Seq(a, b) => expr_effects(a).union(&expr_effects(b)),
        OpExpr::Field(e, _) => expr_effects(e),
        OpExpr::Match {
            scrutinee,
            arms,
            catch_all,
        } => {
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
            body: StepBody::Block(vec![]),
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
        assert!(err.iter().any(|e| matches!(
            e,
            EffectSafetyError::CompensationWithoutCompensableEffect { .. }
        )));
    }

    #[test]
    fn expression_host_call_without_gate_rejected() {
        // §3.9/§4: a write-class effect reachable through a Call expression
        // in Statement::Return must be dominated by a sanctions check.
        let prog = program(vec![Statement::Return(OpExpr::Call(
            "ownership.transfer".to_string(),
            vec![
                ("from".to_string(), OpExpr::String("a".to_string())),
                ("to".to_string(), OpExpr::String("b".to_string())),
            ],
        ))]);
        let err = check_effect_safety(&prog).unwrap_err();
        assert!(
            err.iter().any(|e| matches!(
                e,
                EffectSafetyError::UndominatedWrite { effect, .. } if *effect == Effect::SovereignWrite
            )),
            "expected UndominatedWrite for ownership.transfer; got {err:?}"
        );
    }

    #[test]
    fn unknown_expression_primitive_is_rejected() {
        let prog = program(vec![Statement::Return(OpExpr::Call(
            "opaque.host_write".to_string(),
            vec![],
        ))]);
        let err = check_effect_safety(&prog).unwrap_err();
        assert!(
            err.iter().any(|e| matches!(
                e,
                EffectSafetyError::UnknownPrimitive { primitive, .. }
                    if primitive == "opaque.host_write"
            )),
            "expected UnknownPrimitive; got {err:?}"
        );
    }

    #[test]
    fn unknown_step_primitive_is_rejected_even_with_declared_effects() {
        let step = OpStep {
            id: "fake_gate".to_string(),
            body: StepBody::Primitive(Primitive("opaque.host_write".to_string()), vec![]),
            signature: StepSignature {
                input: OpType::Unit,
                output: OpType::Unit,
                effects: vec![Effect::SanctionsCheck],
            },
            wait: None,
            on_failure: None,
            compensate: None,
            contracts: Contracts::default(),
        };
        let prog = program(vec![Statement::Step(step)]);
        let err = check_effect_safety(&prog).unwrap_err();
        assert!(err.iter().any(|e| matches!(
            e,
            EffectSafetyError::UnknownPrimitive { primitive, site }
                if primitive == "opaque.host_write" && site == "fake_gate"
        )));
    }

    #[test]
    fn declared_step_effects_cannot_fake_sanctions_dominance() {
        let fake_gate = OpStep {
            id: "fake_gate".to_string(),
            body: StepBody::Primitive(Primitive("document.board_minutes".to_string()), vec![]),
            signature: StepSignature {
                input: OpType::Unit,
                output: OpType::Unit,
                effects: vec![Effect::SanctionsCheck],
            },
            wait: None,
            on_failure: None,
            compensate: None,
            contracts: Contracts::default(),
        };
        let write = OpStep {
            id: "write".to_string(),
            body: StepBody::Primitive(Primitive("ownership.transfer".to_string()), vec![]),
            signature: StepSignature {
                input: OpType::Unit,
                output: OpType::Unit,
                effects: vec![Effect::SovereignWrite],
            },
            wait: None,
            on_failure: None,
            compensate: None,
            contracts: Contracts::default(),
        };
        let prog = program(vec![Statement::Step(fake_gate), Statement::Step(write)]);
        let err = check_effect_safety(&prog).unwrap_err();
        assert!(err.iter().any(|e| matches!(
            e,
            EffectSafetyError::UnjustifiedStepEffect {
                step,
                primitive,
                effect
            } if step == "fake_gate"
                && primitive == "document.board_minutes"
                && *effect == Effect::SanctionsCheck
        )));
        assert!(err.iter().any(|e| matches!(
            e,
            EffectSafetyError::UndominatedWrite { step, effect }
                if step == "write" && *effect == Effect::SovereignWrite
        )));
    }

    #[test]
    fn expression_host_call_nested_in_match_rejected() {
        // Embedding the write deep inside Match arms must still be caught.
        let prog = program(vec![Statement::Return(OpExpr::Match {
            scrutinee: Box::new(OpExpr::Bool(true)),
            arms: vec![MatchArm {
                pattern: "true".to_string(),
                binding: "_".to_string(),
                body: OpExpr::Call("fiscal.transfer".to_string(), vec![]),
            }],
            catch_all: Box::new(OpExpr::Unit),
        })]);
        let err = check_effect_safety(&prog).unwrap_err();
        assert!(
            err.iter().any(|e| matches!(
                e,
                EffectSafetyError::UndominatedWrite { effect, .. } if *effect == Effect::FiscalTransfer
            )),
            "expected UndominatedWrite inside Match; got {err:?}"
        );
    }

    #[test]
    fn expression_level_sanctions_then_write_admitted() {
        // Sanctions call earlier in the body makes a later write admissible.
        let prog = program(vec![
            Statement::Expr(OpExpr::Call(
                "sanctions.check".to_string(),
                vec![("principal".to_string(), OpExpr::String("x".to_string()))],
            )),
            Statement::Return(OpExpr::Call("ownership.transfer".to_string(), vec![])),
        ]);
        assert!(check_effect_safety(&prog).is_ok());
    }

    #[test]
    fn seq_sanctions_then_write_is_ordered_and_admitted() {
        let prog = program(vec![Statement::Return(OpExpr::Seq(
            Box::new(OpExpr::Call("sanctions.check".to_string(), vec![])),
            Box::new(OpExpr::Call("ownership.transfer".to_string(), vec![])),
        ))]);
        assert!(check_effect_safety(&prog).is_ok());
    }

    #[test]
    fn run_with_write_call_requires_gate() {
        // A `run` alias to a write-class primitive is equally gated.
        let prog = program(vec![Statement::Run {
            name: "cap".to_string(),
            call: OpExpr::Call("update.cap_table".to_string(), vec![]),
        }]);
        let err = check_effect_safety(&prog).unwrap_err();
        assert!(
            err.iter().any(|e| matches!(
                e,
                EffectSafetyError::UndominatedWrite { effect, .. } if *effect == Effect::SovereignWrite
            )),
            "expected UndominatedWrite on Run of update.cap_table; got {err:?}"
        );
    }

    #[test]
    fn deferred_subject_call_expression_allowed() {
        // An expression-level `create.entity` call carries the deferred-subject
        // exception just like the statement-level form.
        let prog = program(vec![Statement::Return(OpExpr::Call(
            "create.entity".to_string(),
            vec![],
        ))]);
        assert!(check_effect_safety(&prog).is_ok());
    }

    /// The expression-level deferred-subject predicate
    /// (`canonical_is_deferred_subject`) and the statement-level predicate
    /// (`is_entity_create_primitive`) MUST agree on the full canonical
    /// primitive set. A disagreement is the
    /// `deferred-subject-wildcard-mismatch` soundness hazard: a primitive
    /// treated as entity-create (unscreened-write exempt) at one precedence but
    /// not the other lets an unscreened subject slip the sanctions discipline
    /// at the looser level. This test fails the moment either predicate widens
    /// (e.g. a re-introduced `entity.create*` prefix match) without the other.
    #[test]
    fn levels_agree_on_deferred_subject_set() {
        // Every canonical primitive, plus adversarial near-misses that a prefix
        // match would have wrongly admitted.
        let names = [
            "create.entity",
            "update.entity_status",
            "ownership.issue_shares",
            "ownership.transfer",
            "update.cap_table",
            "membership.admit",
            "create.treasury",
            "create.bank_account",
            "fiscal.open_account",
            "fiscal.transfer",
            "identity.verify",
            "consent.board_resolution",
            "consent.member_resolution",
            "consent.shareholder_vote",
            "screening.sanctions",
            "sanctions.check",
            "trade.invoice_create",
            "trade.lc_issue",
            "document.board_minutes",
            "document.shareholder_minutes",
            "document.commercial_invoice",
            "filing.registry_amendment",
            "attestation.append",
            "attestation.emit",
            // Adversarial near-misses: a `starts_with("entity.create")` match
            // would have admitted these as deferred-subject at the step level.
            "entity.create",
            "entity.create_shell",
            "entity.create.bypass",
        ];
        for name in names {
            let expr_level = canonical_is_deferred_subject(name);
            let stmt_level = is_entity_create_primitive(&StepBody::Primitive(
                Primitive(name.to_string()),
                vec![],
            ));
            assert_eq!(
                expr_level, stmt_level,
                "deferred-subject predicate disagreement for '{name}': \
                 expr-level={expr_level} stmt-level={stmt_level}"
            );
        }
        // The exception set is exactly {create.entity}.
        assert!(canonical_is_deferred_subject("create.entity"));
        assert!(!canonical_is_deferred_subject("entity.create"));
        assert!(!is_entity_create_primitive(&StepBody::Primitive(
            Primitive("entity.create_shell".to_string()),
            vec![]
        )));
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
            Statement::Step(step_with_effects("write", vec![Effect::SovereignWrite])),
        ]);
        assert!(check_effect_safety(&prog).is_ok());
    }

    #[test]
    fn compensation_body_write_requires_gate() {
        let mut step = OpStep {
            id: "create".to_string(),
            body: StepBody::Primitive(Primitive("create.entity".to_string()), vec![]),
            signature: StepSignature {
                input: OpType::Unit,
                output: OpType::EntityRef,
                effects: vec![Effect::SovereignWrite],
            },
            wait: None,
            on_failure: None,
            compensate: Some(CompensationClause {
                body: StepBody::Primitive(Primitive("ownership.transfer".to_string()), vec![]),
                invalidated_domains: vec![],
            }),
            contracts: Contracts::default(),
        };
        let prog = program(vec![Statement::Step(step.clone())]);
        let err = check_effect_safety(&prog).unwrap_err();
        assert!(
            err.iter().any(|e| matches!(
                e,
                EffectSafetyError::UndominatedWrite { step, .. }
                    if step == "create:compensate:ownership.transfer"
            )),
            "expected compensation write rejection; got {err:?}"
        );

        step.body = StepBody::Primitive(Primitive("some.op".to_string()), vec![]);
        step.signature.effects = vec![];
        let prog = program(vec![Statement::Step(step)]);
        let err = check_effect_safety(&prog).unwrap_err();
        assert!(
            err.iter().any(|e| matches!(
                e,
                EffectSafetyError::UnknownPrimitive { primitive, site }
                    if primitive == "some.op" && site == "create"
            )),
            "expected unknown primitive rejection; got {err:?}"
        );
    }
}
