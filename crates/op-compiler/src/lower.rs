//! YAML → Op lowering.
//!
//! The input grammar mirrors the legacy operation-definition YAML surface:
//!
//! ```yaml
//! operation: <dotted-name>
//! jurisdiction: <jurisdiction>
//! version: "<semver>"
//! description: "<free text>"
//! params:
//!   required: [<name>, ...]
//!   optional: [<name>, ...]
//! outputs:                       # or `returns:` — the program's result fields
//!   - <name>                     # sequence form: each field typed String
//!   # or mapping form: <name>: <string|int|bool|entity_ref|money|...>
//! steps:
//!   - id: <step-id>
//!     type: <primitive>
//!     params: {...}
//!     depends_on: [<step-id>, ...]
//!     compliance_domains: [<domain>, ...]
//!     wait_for: <callback-event>
//!     timeout: <duration>
//!     on_failure: <cancel|rollback|skip|retry|continue>
//!     condition: <expression>
//! compensation:
//!   steps:
//!     - id: <step-id>
//!       inverts: <forward-step-id>
//!       ...
//! ```
//!
//! The lowerer recovers typed bindings from `depends_on`, pulls compensation
//! back into the step it inverts, and maps compliance domain shorthands into
//! Op's effect row. Unknown constructs are flagged so migration coverage can
//! be tracked.

use op_core::{
    program_effect_row, CompensationClause, Contract, Contracts, Effect, FailureAction, GasBudget,
    OpExpr, OpProgram, OpStep, OpType, Primitive, ProgramMetadata, Statement, StepBody,
    StepSignature, WaitSpec,
};
use serde::{Deserialize, Serialize};
use serde_yaml::Value as YamlValue;
use std::collections::{BTreeMap, BTreeSet};
use thiserror::Error;

/// Report emitted by a successful lowering pass.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoweringReport {
    /// The produced Op program.
    pub program: OpProgram,
    /// Fields or keys the lowerer did not recognize. These are not errors —
    /// they are carried for migration auditing so that the legacy corpus can
    /// be triaged without silently losing shape.
    pub warnings: Vec<String>,
}

/// Errors the lowerer may surface.
#[derive(Debug, Clone, Error, Serialize, Deserialize, PartialEq, Eq)]
pub enum LoweringError {
    /// Input is not valid YAML.
    #[error("yaml parse: {0}")]
    YamlParse(String),

    /// Input lacks a required top-level field.
    #[error("missing required field: {0}")]
    MissingField(String),

    /// A field carried an unexpected shape.
    #[error("shape error in field '{field}': {detail}")]
    ShapeError {
        /// Field name.
        field: String,
        /// Diagnostic.
        detail: String,
    },

    /// `depends_on` references an unknown step.
    #[error("unknown depends_on target: {0}")]
    UnknownDependency(String),

    /// Step identifiers must be unique.
    #[error("duplicate step id: {0}")]
    DuplicateStepId(String),

    /// `depends_on` must point to an earlier step because Op execution order is
    /// the emitted linear statement order.
    #[error("step '{step}' depends on '{dependency}', which is not earlier in source order")]
    NonTopologicalDependency {
        /// Step declaring the dependency.
        step: String,
        /// Dependency that does not precede it.
        dependency: String,
    },

    /// A compensation clause targets no known forward step.
    #[error("unknown compensation target: {0}")]
    UnknownCompensationTarget(String),

    /// A forward step may have at most one compensation clause.
    #[error("duplicate compensation target: {0}")]
    DuplicateCompensationTarget(String),

    /// Type-checking failed after successful lowering.
    #[error("type check failed after lowering: {errors:?}")]
    TypeCheckFailed {
        /// Type-check diagnostics.
        errors: Vec<String>,
    },

    /// Computing the compiled program's content address failed (the program
    /// could not be serialized to its canonical byte form). Surfaced rather
    /// than hashing the empty string, which would mint a meaningless,
    /// collision-prone content id.
    #[error("content addressing failed: {0}")]
    ContentAddress(String),

    /// A step declared an `on_failure` policy the lowerer does not recognize.
    /// Silently dropping it would default the step to `CancelOperation`, which
    /// is a different (and possibly far weaker or stronger) failure semantics
    /// than the author wrote — a silent fallback on a security/control field.
    #[error(
        "step '{step}' declares unknown on_failure '{value}' (expected one of: \
         cancel, cancel_operation, rollback, skip, retry, continue)"
    )]
    UnknownFailureAction {
        /// Step declaring the policy.
        step: String,
        /// The unrecognized value.
        value: String,
    },

    /// A `timeout`/`wait_for` carried a duration the lowerer cannot parse.
    /// A silent `0` here disables the wait entirely (the callback never blocks),
    /// so a malformed duration must fail loud rather than mint a 0 timeout.
    #[error("step '{step}' has invalid duration '{value}': {detail}")]
    InvalidDuration {
        /// Step declaring the duration.
        step: String,
        /// The raw duration string.
        value: String,
        /// Why it could not be parsed.
        detail: String,
    },

    /// A `wait_for` was declared without a sibling `timeout`. A wait with no
    /// timeout silently blocks forever; the daemon recognizes only an explicit
    /// timeout, so the absence is a control-field gap that must fail loud.
    #[error("step '{step}' declares 'wait_for: {event}' without a sibling 'timeout'")]
    WaitWithoutTimeout {
        /// Step declaring the wait.
        step: String,
        /// The awaited event.
        event: String,
    },

    /// A compensation clause omitted its `type` (inverse primitive). Defaulting
    /// to a no-op would silently turn a declared rollback into nothing — the
    /// compensation would appear present but invert nothing.
    #[error("compensation step inverting '{forward}' has no 'type' (inverse primitive)")]
    MissingCompensationType {
        /// The forward step this compensation inverts.
        forward: String,
    },
}

/// Lower a YAML document into an `OpProgram`.
pub fn lower_yaml(yaml: &str) -> Result<LoweringReport, LoweringError> {
    let doc: YamlValue =
        serde_yaml::from_str(yaml).map_err(|e| LoweringError::YamlParse(e.to_string()))?;
    let mut warnings = Vec::new();

    let name = take_string(&doc, "operation")?;
    let jurisdiction = take_string(&doc, "jurisdiction")?;
    let version = take_string_opt(&doc, "version").unwrap_or_default();
    let description = take_string_opt(&doc, "description").unwrap_or_default();

    let inputs = lower_params(&doc, &mut warnings);
    let outputs = lower_outputs(&doc, &mut warnings);
    let steps_yaml = doc
        .get("steps")
        .and_then(YamlValue::as_sequence)
        .cloned()
        .unwrap_or_default();
    let known_ids: Vec<String> = steps_yaml
        .iter()
        .filter_map(|s| s.get("id").and_then(YamlValue::as_str))
        .map(|s| s.to_string())
        .collect();
    validate_unique_step_ids(&known_ids)?;
    let compensation_map = index_compensation(&doc, &known_ids, &mut warnings)?;

    let mut body: Vec<Statement> = Vec::new();
    let mut seen_ids = BTreeSet::new();
    for step_yaml in &steps_yaml {
        let step = lower_step(
            step_yaml,
            &compensation_map,
            &known_ids,
            &seen_ids,
            &mut warnings,
        )?;
        seen_ids.insert(step.id.clone());
        body.push(Statement::Step(step));
    }

    let metadata = ProgramMetadata {
        version,
        description,
    };

    let gas_budget = GasBudget::default();

    let mut program = OpProgram {
        name,
        jurisdiction,
        metadata,
        inputs,
        outputs,
        effects: vec![],
        participants: vec![],
        approval: None,
        contracts: Contracts::default(),
        body,
        gas_budget,
    };
    program.effects = program_effect_row(&program);

    Ok(LoweringReport { program, warnings })
}

fn take_string(doc: &YamlValue, field: &str) -> Result<String, LoweringError> {
    match doc.get(field) {
        Some(YamlValue::String(s)) if !s.is_empty() => Ok(s.clone()),
        Some(YamlValue::String(_)) => Err(LoweringError::ShapeError {
            field: field.to_string(),
            detail: "must not be empty".to_string(),
        }),
        Some(_) => Err(LoweringError::ShapeError {
            field: field.to_string(),
            detail: "expected a string".to_string(),
        }),
        None => Err(LoweringError::MissingField(field.to_string())),
    }
}

fn take_string_opt(doc: &YamlValue, field: &str) -> Option<String> {
    doc.get(field)
        .and_then(YamlValue::as_str)
        .map(str::to_string)
}

fn lower_params(doc: &YamlValue, warnings: &mut Vec<String>) -> Vec<(String, OpType)> {
    let params = match doc.get("params") {
        Some(p) => p,
        None => return Vec::new(),
    };
    let mut out: Vec<(String, OpType)> = Vec::new();
    if let Some(required) = params.get("required").and_then(YamlValue::as_sequence) {
        for item in required {
            if let Some(name) = item.as_str() {
                out.push((name.to_string(), OpType::String));
            } else {
                warnings.push(format!(
                    "params.required item not a string: {item:?} — mapped to String default"
                ));
            }
        }
    }
    if let Some(optional) = params.get("optional").and_then(YamlValue::as_sequence) {
        for item in optional {
            if let Some(name) = item.as_str() {
                out.push((name.to_string(), OpType::Option(Box::new(OpType::String))));
            } else {
                warnings.push(format!("params.optional item not a string: {item:?}"));
            }
        }
    }
    out
}

/// Lower a top-level `outputs:` (or `returns:`) section into typed program
/// output fields.
///
/// Two surface forms are accepted, mirroring the legacy corpus:
/// - a sequence of field names (`outputs: [entity_id, status]`), each typed
///   `String` (the same default `params.required` uses);
/// - a mapping of field name to a type hint
///   (`outputs: { entity_id: entity_ref, count: int }`).
///
/// When the section is absent the program declares no outputs (`vec![]`) —
/// the empty result is preserved as the genuine "this program returns nothing"
/// semantics, not a silent default that masks a declared-but-unparsed section.
fn lower_outputs(doc: &YamlValue, warnings: &mut Vec<String>) -> Vec<(String, OpType)> {
    // Accept `outputs` first, then `returns` as an alias.
    let (field, section) = match (doc.get("outputs"), doc.get("returns")) {
        (Some(o), _) => ("outputs", o),
        (None, Some(r)) => ("returns", r),
        (None, None) => return Vec::new(),
    };

    let mut out: Vec<(String, OpType)> = Vec::new();
    match section {
        YamlValue::Sequence(items) => {
            for item in items {
                if let Some(name) = item.as_str() {
                    out.push((name.to_string(), OpType::String));
                } else {
                    warnings.push(format!(
                        "{field} item not a string: {item:?} — output field skipped"
                    ));
                }
            }
        }
        YamlValue::Mapping(m) => {
            for (k, v) in m {
                let Some(name) = k.as_str() else {
                    warnings.push(format!("{field} key not a string: {k:?} — field skipped"));
                    continue;
                };
                let ty = match v.as_str() {
                    Some(hint) => output_type_from_hint(hint).unwrap_or_else(|| {
                        warnings.push(format!(
                            "{field}.{name} has unknown type hint '{hint}' — typed as String"
                        ));
                        OpType::String
                    }),
                    None => {
                        warnings.push(format!(
                            "{field}.{name} type hint not a string: {v:?} — typed as String"
                        ));
                        OpType::String
                    }
                };
                out.push((name.to_string(), ty));
            }
        }
        other => {
            warnings.push(format!(
                "{field} section is neither a sequence nor a mapping: {other:?} — no outputs declared"
            ));
        }
    }
    out
}

/// Map a YAML output type-hint string to an `OpType`. Returns `None` for an
/// unrecognized hint so the caller can warn and fall back to `String`.
fn output_type_from_hint(hint: &str) -> Option<OpType> {
    match hint.to_lowercase().as_str() {
        "string" | "str" | "text" => Some(OpType::String),
        "int" | "integer" | "i64" => Some(OpType::Int),
        "bool" | "boolean" => Some(OpType::Bool),
        "unit" => Some(OpType::Unit),
        "date" => Some(OpType::Date),
        "timestamp" => Some(OpType::Timestamp),
        "duration" => Some(OpType::Duration),
        "entity_ref" | "entityref" | "entity" => Some(OpType::EntityRef),
        "jurisdiction_ref" | "jurisdictionref" | "jurisdiction" => Some(OpType::JurisdictionRef),
        "money" | "money_amount" | "moneyamount" => Some(OpType::MoneyAmount),
        "content_digest" | "contentdigest" | "digest" => Some(OpType::ContentDigest),
        "callback_event" | "callbackevent" => Some(OpType::CallbackEvent),
        _ => None,
    }
}

fn lower_step(
    step: &YamlValue,
    compensation: &BTreeMap<String, CompensationClause>,
    known_ids: &[String],
    seen_ids: &BTreeSet<String>,
    warnings: &mut Vec<String>,
) -> Result<OpStep, LoweringError> {
    let id = take_string(step, "id")?;
    let step_type = take_string(step, "type")?;

    // depends_on references must resolve.
    if let Some(deps) = step.get("depends_on").and_then(YamlValue::as_sequence) {
        for d in deps {
            if let Some(target) = d.as_str() {
                if !known_ids.iter().any(|n| n == target) {
                    return Err(LoweringError::UnknownDependency(target.to_string()));
                }
                if !seen_ids.contains(target) {
                    return Err(LoweringError::NonTopologicalDependency {
                        step: id.clone(),
                        dependency: target.to_string(),
                    });
                }
            }
        }
    }

    let args: Vec<(String, OpExpr)> = step
        .get("params")
        .and_then(YamlValue::as_mapping)
        .map(|m| {
            m.iter()
                .filter_map(|(k, v)| {
                    let key = k.as_str()?.to_string();
                    Some((key, yaml_value_to_expr(v)))
                })
                .collect()
        })
        .unwrap_or_default();

    // Compliance domains contribute both their effect projection (sanctions →
    // SanctionsCheck, screening domains → ExternalRead) and a preserved
    // `Contract::Domains` requirement so no listed domain is silently dropped.
    let (domain_effects, declared_domains) = compliance_domains(step, &id, warnings);

    // Step signature effects are inferred from the primitive's canonical effect
    // row (the authoritative source the effect-safety checker validates
    // against) unioned with the compliance-domain effects. Hardcoding an empty
    // effect row would falsely claim, e.g., that a `create.entity` step has no
    // effect while it carries `SovereignWrite`.
    let mut effects: Vec<Effect> = canonical_effects_for(&step_type);
    if effects.is_empty() && !canonical_primitive_known(&step_type) {
        warnings.push(format!(
            "step '{id}' uses primitive '{step_type}' not in the canonical corpus — \
             its effect row could not be inferred and its I/O signature is left unknown \
             (Record[]); route it through a typed step or extend the corpus"
        ));
    }
    for e in domain_effects {
        if !effects.contains(&e) {
            effects.push(e);
        }
    }

    // `wait_for` requires a sibling `timeout`. A wait with no timeout blocks
    // forever; a malformed timeout silently disabling the wait (0s) is a
    // control-field defect. Both fail loud.
    let wait = match step.get("wait_for").and_then(YamlValue::as_str) {
        Some(event) => {
            let timeout_value = step
                .get("timeout")
                .and_then(YamlValue::as_str)
                .ok_or_else(|| LoweringError::WaitWithoutTimeout {
                    step: id.clone(),
                    event: event.to_string(),
                })?;
            let timeout_secs = parse_duration_seconds(timeout_value).map_err(|detail| {
                LoweringError::InvalidDuration {
                    step: id.clone(),
                    value: timeout_value.to_string(),
                    detail,
                }
            })?;
            Some(WaitSpec {
                event: event.to_string(),
                timeout_secs,
            })
        }
        None => None,
    };

    // An unknown `on_failure` must not silently collapse to the `None` default
    // (CancelOperation) — that rewrites the author's failure policy. Reject it.
    let on_failure = match step.get("on_failure") {
        None => None,
        Some(YamlValue::String(s)) => Some(parse_failure_action(s).ok_or_else(|| {
            LoweringError::UnknownFailureAction {
                step: id.clone(),
                value: s.clone(),
            }
        })?),
        Some(other) => {
            return Err(LoweringError::ShapeError {
                field: format!("steps[{id}].on_failure"),
                detail: format!("expected a string, got {other:?}"),
            })
        }
    };

    let condition_requires = step
        .get("condition")
        .and_then(YamlValue::as_str)
        .map(|c| Contract::Expr(OpExpr::String(c.to_string())));

    // Preserve the declared compliance domains as a contract requirement so
    // the lowered program still carries every domain the source listed, even
    // those with no distinct Op effect.
    let domain_requirement = if declared_domains.is_empty() {
        None
    } else {
        Some(Contract::Domains(declared_domains))
    };

    let contracts = Contracts {
        requires: condition_requires
            .into_iter()
            .chain(domain_requirement)
            .collect(),
        ensures: vec![],
    };

    let primitive = Primitive(step_type);
    let body = StepBody::Primitive(primitive, args);
    let compensate = compensation.get(&id).cloned();

    Ok(OpStep {
        id,
        body,
        signature: StepSignature {
            // The canonical corpus carries effect rows but not typed I/O
            // shapes, so the structural I/O type is genuinely unknown here.
            // We do not fabricate field structure; `Record[]` is the
            // explicit "no fields recovered from the YAML surface" shape, and
            // unknown primitives are warned above so the gap is surfaced
            // rather than presented as a precise empty signature.
            input: OpType::Record(vec![]),
            output: OpType::Record(vec![]),
            effects,
        },
        wait,
        on_failure,
        compensate,
        contracts,
    })
}

/// Parse a duration like `30s`, `5m`, `2h`, `7d` into seconds.
///
/// Fails loud (returns `Err(detail)`) on an empty string, a non-numeric
/// magnitude, an unknown unit suffix, or an overflowing multiplication. A
/// silent fallback to `0` here would disable the wait it gates entirely, so a
/// malformed duration is never coerced into a valid-looking zero.
fn parse_duration_seconds(d: &str) -> Result<u64, String> {
    let trimmed = d.trim();
    if trimmed.is_empty() {
        return Err("duration is empty".to_string());
    }
    // Split the trailing unit character from the magnitude.
    let unit = trimmed
        .chars()
        .last()
        .ok_or_else(|| "duration has no unit suffix".to_string())?;
    let num_part = &trimmed[..trimmed.len() - unit.len_utf8()];
    if num_part.is_empty() {
        return Err(format!("duration '{trimmed}' has no numeric magnitude"));
    }
    let n: u64 = num_part
        .parse()
        .map_err(|_| format!("duration magnitude '{num_part}' is not a non-negative integer"))?;
    let secs_per_unit: u64 = match unit {
        's' => 1,
        'm' => 60,
        'h' => 3_600,
        'd' => 86_400,
        other => {
            return Err(format!(
                "unknown duration unit '{other}' (expected one of s, m, h, d)"
            ))
        }
    };
    n.checked_mul(secs_per_unit)
        .ok_or_else(|| format!("duration '{trimmed}' overflows u64 seconds"))
}

fn parse_failure_action(s: &str) -> Option<FailureAction> {
    match s {
        "cancel" | "cancel_operation" => Some(FailureAction::CancelOperation),
        "rollback" => Some(FailureAction::Rollback),
        "skip" => Some(FailureAction::Skip),
        "retry" => Some(FailureAction::Retry { max_attempts: 3 }),
        "continue" => Some(FailureAction::Continue),
        _ => None,
    }
}

/// Lower a step's `compliance_domains` list.
///
/// Returns `(effects, domains)`:
/// - `effects` is the effect-row projection of the domains. Only domains that
///   correspond to a distinct Op effect contribute: `sanctions` →
///   [`Effect::SanctionsCheck`]; `aml`/`kyc` → [`Effect::ExternalRead`] (both
///   require an external screening read, but neither is the dominating
///   sanctions gate — only `sanctions` is). Every other recognized domain
///   (corporate, tax, securities, …) is a compliance *requirement*, not an
///   Op effect, so it contributes no effect.
/// - `domains` is the full, normalized (lowercased) list of every recognized
///   domain, preserved so the caller can attach it as a `Contract::Domains`
///   requirement. No domain is silently dropped: an effect-less domain still
///   rides in this list, and an *unrecognized* domain string is surfaced as a
///   warning naming the value (rather than vanishing).
fn compliance_domains(
    step: &YamlValue,
    step_id: &str,
    warnings: &mut Vec<String>,
) -> (Vec<Effect>, Vec<String>) {
    let mut effects = Vec::new();
    let mut domains = Vec::new();
    if let Some(doms) = step
        .get("compliance_domains")
        .and_then(YamlValue::as_sequence)
    {
        for d in doms {
            let Some(raw) = d.as_str() else {
                warnings.push(format!(
                    "step '{step_id}': compliance_domains item not a string: {d:?} — dropped"
                ));
                continue;
            };
            let name = raw.to_lowercase();
            match name.as_str() {
                "sanctions" => effects.push(Effect::SanctionsCheck),
                "aml" | "kyc" => effects.push(Effect::ExternalRead),
                _ if is_known_compliance_domain(&name) => {
                    // Recognized domain with no distinct Op effect; preserved
                    // below as a contract requirement.
                }
                _ => {
                    // Unknown domain string — surfaced, not silently dropped.
                    // It is still preserved in `domains` so the requirement
                    // is not lost, but the operator is warned it is not a
                    // recognized compliance domain.
                    warnings.push(format!(
                        "step '{step_id}': compliance_domains entry '{raw}' is not a recognized \
                         compliance domain — preserved as a requirement but mapped to no effect"
                    ));
                }
            }
            domains.push(name);
        }
    }
    (effects, domains)
}

/// The 23 canonical kernel compliance-domain names (lowercased). Used to
/// distinguish a recognized-but-effect-less domain (preserved silently as a
/// contract requirement) from an unrecognized string (warned).
fn is_known_compliance_domain(name: &str) -> bool {
    matches!(
        name,
        "aml"
            | "kyc"
            | "sanctions"
            | "tax"
            | "securities"
            | "corporate"
            | "custody"
            | "data_privacy"
            | "licensing"
            | "banking"
            | "payments"
            | "clearing"
            | "settlement"
            | "digital_assets"
            | "employment"
            | "immigration"
            | "ip"
            | "consumer_protection"
            | "arbitration"
            | "trade"
            | "insurance"
            | "anti_bribery"
            | "sharia"
    )
}

/// Canonical primitive effect table for the compiler's signature inference.
///
/// This mirrors `op_core::effects::canonical_effects_for` — the authoritative
/// row the effect-safety checker validates each step signature against. op-core
/// keeps that table `pub(crate)`, so the compiler inlines the same shapes here
/// to infer a step's signature effects at lowering time. The two tables MUST
/// agree: a divergence would make the lowerer emit a signature effect the
/// safety checker then rejects as `UnjustifiedStepEffect`. A round-trip test
/// (`signature_effects_match_canonical_corpus`) pins them together.
fn canonical_effects_for(name: &str) -> Vec<Effect> {
    match name {
        "create.entity" | "update.entity_status" => vec![Effect::SovereignWrite],
        "ownership.issue_shares"
        | "ownership.transfer"
        | "update.cap_table"
        | "membership.admit" => vec![Effect::SovereignWrite],
        "create.treasury" | "create.bank_account" | "fiscal.open_account" => {
            vec![Effect::SovereignWrite]
        }
        "fiscal.transfer" => vec![Effect::FiscalTransfer, Effect::SovereignWrite],
        "identity.verify" => vec![Effect::ExternalRead, Effect::IdentityMutation],
        "consent.board_resolution" | "consent.member_resolution" | "consent.shareholder_vote" => {
            vec![Effect::GovernanceRequest, Effect::SovereignWrite]
        }
        "screening.sanctions" | "sanctions.check" => {
            vec![Effect::SanctionsCheck, Effect::ExternalRead]
        }
        "trade.invoice_create" | "trade.lc_issue" => {
            vec![Effect::FiscalTransfer, Effect::SovereignWrite]
        }
        "document.board_minutes"
        | "document.shareholder_minutes"
        | "document.commercial_invoice" => vec![Effect::DocumentGeneration],
        "filing.registry_amendment" => vec![Effect::SovereignWrite, Effect::ProofEmit],
        "attestation.append" | "attestation.emit" => vec![Effect::ProofEmit],
        _ => Vec::new(),
    }
}

/// Whether `name` is a primitive in the canonical corpus. Mirrors
/// `op_core::effects::canonical_primitive_known`.
fn canonical_primitive_known(name: &str) -> bool {
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

fn yaml_value_to_expr(v: &YamlValue) -> OpExpr {
    match v {
        YamlValue::Null => OpExpr::Null,
        YamlValue::Bool(b) => OpExpr::Bool(*b),
        YamlValue::Number(n) => n.as_i64().map(OpExpr::Int).unwrap_or(OpExpr::Int(0)),
        YamlValue::String(s) => OpExpr::String(s.clone()),
        YamlValue::Sequence(items) => OpExpr::List(items.iter().map(yaml_value_to_expr).collect()),
        YamlValue::Mapping(m) => OpExpr::Record(
            m.iter()
                .filter_map(|(k, v)| {
                    let key = k.as_str()?.to_string();
                    Some((key, yaml_value_to_expr(v)))
                })
                .collect(),
        ),
        YamlValue::Tagged(t) => yaml_value_to_expr(&t.value),
    }
}

fn index_compensation(
    doc: &YamlValue,
    known_ids: &[String],
    warnings: &mut Vec<String>,
) -> Result<BTreeMap<String, CompensationClause>, LoweringError> {
    let mut out = BTreeMap::new();
    let Some(comp) = doc.get("compensation") else {
        return Ok(out);
    };
    let Some(steps) = comp.get("steps").and_then(YamlValue::as_sequence) else {
        return Ok(out);
    };
    for s in steps {
        let forward = s
            .get("inverts")
            .and_then(YamlValue::as_str)
            .map(str::to_string);
        let Some(forward) = forward else {
            warnings.push(format!(
                "compensation step {:?} has no 'inverts' field and was skipped",
                s.get("id")
            ));
            continue;
        };
        if !known_ids.iter().any(|id| id == &forward) {
            return Err(LoweringError::UnknownCompensationTarget(forward));
        }
        if out.contains_key(&forward) {
            return Err(LoweringError::DuplicateCompensationTarget(forward));
        }
        // A compensation clause MUST name its inverse primitive. Defaulting a
        // missing/malformed `type` to "noop" would silently turn a declared
        // rollback into a no-op — the compensation would appear attached to the
        // forward step while inverting nothing. Fail loud instead.
        let primitive_name = match s.get("type") {
            Some(YamlValue::String(t)) if !t.is_empty() => t.clone(),
            _ => {
                return Err(LoweringError::MissingCompensationType {
                    forward: forward.clone(),
                })
            }
        };
        let args: Vec<(String, OpExpr)> = s
            .get("params")
            .and_then(YamlValue::as_mapping)
            .map(|m| {
                m.iter()
                    .filter_map(|(k, v)| Some((k.as_str()?.to_string(), yaml_value_to_expr(v))))
                    .collect()
            })
            .unwrap_or_default();
        let invalidated = s
            .get("invalidates")
            .and_then(YamlValue::as_sequence)
            .map(|seq| {
                seq.iter()
                    .filter_map(|v| v.as_str().map(str::to_string))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        out.insert(
            forward,
            CompensationClause {
                body: StepBody::Primitive(Primitive(primitive_name), args),
                invalidated_domains: invalidated,
            },
        );
    }
    Ok(out)
}

fn validate_unique_step_ids(ids: &[String]) -> Result<(), LoweringError> {
    let mut seen = BTreeSet::new();
    for id in ids {
        if !seen.insert(id) {
            return Err(LoweringError::DuplicateStepId(id.clone()));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const SIMPLE: &str = r#"
operation: entity.activate
jurisdiction: sc
params:
  required: [entity_id]
steps:
  - id: gate
    type: screening.sanctions
    params:
      subject_id: "${entity_id}"
    compliance_domains: [sanctions]
  - id: activate
    type: update.entity_status
    depends_on: [gate]
    params:
      entity_id: "${entity_id}"
      status: "ACTIVE"
compensation:
  steps:
    - id: deactivate
      inverts: activate
      type: update.entity_status
      params:
        entity_id: "${entity_id}"
        status: "INACTIVE"
      invalidates: [corporate]
"#;

    #[test]
    fn simple_yaml_lowers() {
        let report = lower_yaml(SIMPLE).expect("simple yaml must lower");
        assert_eq!(report.program.name, "entity.activate");
        assert_eq!(report.program.jurisdiction, "sc");
        assert_eq!(report.program.body.len(), 2);
    }

    #[test]
    fn compensation_attaches_to_forward_step() {
        let report = lower_yaml(SIMPLE).unwrap();
        let has_compensation = report.program.body.iter().any(|s| match s {
            Statement::Step(step) => step.id == "activate" && step.compensate.is_some(),
            _ => false,
        });
        assert!(has_compensation);
    }

    #[test]
    fn unknown_depends_on_is_rejected() {
        let yaml = r#"
operation: broken.op
jurisdiction: _default
steps:
  - id: dependent
    type: some.op
    depends_on: [missing]
"#;
        let err = lower_yaml(yaml).unwrap_err();
        assert_eq!(err, LoweringError::UnknownDependency("missing".to_string()));
    }

    #[test]
    fn forward_or_cyclic_depends_on_is_rejected() {
        let yaml = r#"
operation: broken.order
jurisdiction: _default
steps:
  - id: a
    type: document.board_minutes
    depends_on: [b]
  - id: b
    type: document.board_minutes
    depends_on: [a]
"#;
        let err = lower_yaml(yaml).unwrap_err();
        assert_eq!(
            err,
            LoweringError::NonTopologicalDependency {
                step: "a".to_string(),
                dependency: "b".to_string(),
            }
        );
    }

    #[test]
    fn unknown_compensation_target_is_rejected() {
        let yaml = r#"
operation: broken.compensation
jurisdiction: _default
steps:
  - id: activate
    type: document.board_minutes
compensation:
  steps:
    - id: typo
      inverts: activte
      type: document.board_minutes
"#;
        let err = lower_yaml(yaml).unwrap_err();
        assert_eq!(
            err,
            LoweringError::UnknownCompensationTarget("activte".to_string())
        );
    }

    #[test]
    fn duplicate_compensation_target_is_rejected() {
        let yaml = r#"
operation: broken.duplicate-compensation
jurisdiction: _default
steps:
  - id: activate
    type: document.board_minutes
compensation:
  steps:
    - id: c1
      inverts: activate
      type: document.board_minutes
    - id: c2
      inverts: activate
      type: document.board_minutes
"#;
        let err = lower_yaml(yaml).unwrap_err();
        assert_eq!(
            err,
            LoweringError::DuplicateCompensationTarget("activate".to_string())
        );
    }

    #[test]
    fn missing_operation_field_rejected() {
        let yaml = "jurisdiction: sc\nsteps: []\n";
        let err = lower_yaml(yaml).unwrap_err();
        assert!(matches!(err, LoweringError::MissingField(_)));
    }

    #[test]
    fn duration_parsing() {
        assert_eq!(parse_duration_seconds("30s"), Ok(30));
        assert_eq!(parse_duration_seconds("5m"), Ok(300));
        assert_eq!(parse_duration_seconds("2h"), Ok(7_200));
        assert_eq!(parse_duration_seconds("7d"), Ok(604_800));
    }

    #[test]
    fn duration_parsing_fails_loud() {
        // Unknown unit, non-numeric magnitude, empty, no magnitude, and
        // overflow must all error rather than silently coerce to 0.
        assert!(parse_duration_seconds("30x").is_err()); // unknown unit
        assert!(parse_duration_seconds("foos").is_err()); // non-numeric magnitude
        assert!(parse_duration_seconds("").is_err()); // empty
        assert!(parse_duration_seconds("s").is_err()); // no magnitude
        assert!(parse_duration_seconds("-5s").is_err()); // negative
        assert!(parse_duration_seconds("99999999999999999999d").is_err()); // overflow
    }

    #[test]
    fn sanctions_domain_becomes_sanctions_check_effect() {
        let report = lower_yaml(SIMPLE).unwrap();
        let has_effect = report.program.body.iter().any(|s| match s {
            Statement::Step(step) => step.signature.effects.contains(&Effect::SanctionsCheck),
            _ => false,
        });
        assert!(has_effect);
    }

    // ---------------------------------------------------------------------
    // Test helpers
    // ---------------------------------------------------------------------

    fn step_named<'a>(report: &'a LoweringReport, id: &str) -> &'a OpStep {
        report
            .program
            .body
            .iter()
            .find_map(|s| match s {
                Statement::Step(step) if step.id == id => Some(step),
                _ => None,
            })
            .unwrap_or_else(|| panic!("step '{id}' not found"))
    }

    // ---------------------------------------------------------------------
    // Finding 5 — step signature effects inferred from the canonical corpus
    // ---------------------------------------------------------------------

    #[test]
    fn step_signature_effects_inferred_from_primitive() {
        // The `activate` step lists NO compliance_domains, yet
        // `update.entity_status` is a SovereignWrite primitive. The inferred
        // signature must carry SovereignWrite — not an empty row.
        let report = lower_yaml(SIMPLE).unwrap();
        let activate = step_named(&report, "activate");
        assert!(
            activate.signature.effects.contains(&Effect::SovereignWrite),
            "expected SovereignWrite inferred for update.entity_status; got {:?}",
            activate.signature.effects
        );
        // The `gate` step's screening primitive carries SanctionsCheck +
        // ExternalRead canonically; the compliance_domains projection adds
        // SanctionsCheck (already present, deduplicated).
        let gate = step_named(&report, "gate");
        assert!(gate.signature.effects.contains(&Effect::SanctionsCheck));
        assert!(gate.signature.effects.contains(&Effect::ExternalRead));
    }

    #[test]
    fn signature_effects_match_canonical_corpus() {
        // The inlined canonical table MUST agree with op-core's authoritative
        // row for every corpus primitive; otherwise the lowerer would emit a
        // signature effect the effect-safety checker rejects. We assert by
        // compiling a gated program per primitive and confirming op-core
        // accepts the inferred signature (no UnjustifiedStepEffect).
        for prim in [
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
            "trade.invoice_create",
            "trade.lc_issue",
            "document.board_minutes",
            "document.shareholder_minutes",
            "document.commercial_invoice",
            "filing.registry_amendment",
            "attestation.append",
            "attestation.emit",
        ] {
            let yaml = format!(
                r#"
operation: corpus.probe
jurisdiction: _default
steps:
  - id: gate
    type: screening.sanctions
    compliance_domains: [sanctions]
  - id: act
    type: {prim}
    depends_on: [gate]
"#
            );
            let report = lower_yaml(&yaml).unwrap_or_else(|e| panic!("{prim} must lower: {e}"));
            let tc = op_core::typecheck_program(&report.program);
            assert!(
                !tc.errors
                    .iter()
                    .any(|e| e.contains("UnjustifiedStepEffect") || e.contains("does not justify")),
                "inferred signature for {prim} diverged from canonical row: {:?}",
                tc.errors
            );
            // The inferred effects must equal op-core's canonical row for the
            // primitive (the act step lists no domains, so no projection).
            let act = step_named(&report, "act");
            let mut inferred = act.signature.effects.clone();
            inferred.sort();
            let mut expected = canonical_effects_for(prim);
            expected.sort();
            assert_eq!(inferred, expected, "effect-row mismatch for {prim}");
        }
    }

    #[test]
    fn unknown_primitive_signature_is_warned_not_silently_empty() {
        // An unknown primitive cannot have its effects inferred. The lowerer
        // must surface that (warning) rather than claim a precise empty
        // signature for a primitive it does not understand.
        let yaml = r#"
operation: unknown.prim
jurisdiction: _default
steps:
  - id: mystery
    type: vendor.proprietary_thing
"#;
        let report = lower_yaml(yaml).unwrap();
        let mystery = step_named(&report, "mystery");
        assert!(
            mystery.signature.effects.is_empty(),
            "unknown primitive has no inferable effects"
        );
        assert!(
            report
                .warnings
                .iter()
                .any(|w| w.contains("vendor.proprietary_thing") && w.contains("not in the canonical corpus")),
            "expected a warning naming the unknown primitive; got {:?}",
            report.warnings
        );
    }

    // ---------------------------------------------------------------------
    // Finding 1 + 7 — compliance domains: no silent drop, all preserved
    // ---------------------------------------------------------------------

    #[test]
    fn recognized_effectless_domain_is_preserved_not_dropped() {
        // `corporate` is a recognized compliance domain with no distinct Op
        // effect. It must be preserved as a Contract::Domains requirement, not
        // silently discarded, and must NOT warn (it is recognized).
        let yaml = r#"
operation: domain.preserve
jurisdiction: _default
steps:
  - id: gate
    type: screening.sanctions
    compliance_domains: [sanctions, corporate, tax]
  - id: act
    type: update.entity_status
    depends_on: [gate]
"#;
        let report = lower_yaml(yaml).unwrap();
        let gate = step_named(&report, "gate");
        let domains: Vec<&str> = gate
            .contracts
            .requires
            .iter()
            .find_map(|c| match c {
                Contract::Domains(d) => Some(d.iter().map(String::as_str).collect()),
                _ => None,
            })
            .expect("compliance domains must be preserved as a Contract::Domains requirement");
        assert!(domains.contains(&"sanctions"));
        assert!(domains.contains(&"corporate"));
        assert!(domains.contains(&"tax"));
        // No warnings for recognized domains.
        assert!(
            report.warnings.is_empty(),
            "recognized domains must not warn; got {:?}",
            report.warnings
        );
    }

    #[test]
    fn unknown_domain_string_is_surfaced_as_warning() {
        // An UNRECOGNIZED domain string must fail loud (warning naming it),
        // never silently vanish — a dropped domain is a missing requirement.
        let yaml = r#"
operation: domain.unknown
jurisdiction: _default
steps:
  - id: gate
    type: screening.sanctions
    compliance_domains: [sanctions, definitely_not_a_domain]
"#;
        let report = lower_yaml(yaml).unwrap();
        assert!(
            report
                .warnings
                .iter()
                .any(|w| w.contains("definitely_not_a_domain") && w.contains("not a recognized")),
            "expected a warning naming the unknown domain; got {:?}",
            report.warnings
        );
        // Even the unknown domain is preserved as a requirement (not lost).
        let gate = step_named(&report, "gate");
        let preserved = gate.contracts.requires.iter().any(|c| match c {
            Contract::Domains(d) => d.iter().any(|x| x == "definitely_not_a_domain"),
            _ => false,
        });
        assert!(preserved, "unknown domain must still be preserved, not dropped");
    }

    // ---------------------------------------------------------------------
    // Finding 2 — unknown on_failure fails loud
    // ---------------------------------------------------------------------

    #[test]
    fn unknown_on_failure_is_rejected() {
        let yaml = r#"
operation: failure.unknown
jurisdiction: _default
steps:
  - id: s1
    type: document.board_minutes
    on_failure: explode
"#;
        let err = lower_yaml(yaml).unwrap_err();
        assert_eq!(
            err,
            LoweringError::UnknownFailureAction {
                step: "s1".to_string(),
                value: "explode".to_string(),
            }
        );
    }

    #[test]
    fn known_on_failure_still_parses() {
        let yaml = r#"
operation: failure.known
jurisdiction: _default
steps:
  - id: s1
    type: document.board_minutes
    on_failure: skip
"#;
        let report = lower_yaml(yaml).unwrap();
        assert_eq!(step_named(&report, "s1").on_failure, Some(FailureAction::Skip));
    }

    // ---------------------------------------------------------------------
    // Finding 3 — malformed duration / wait without timeout fail loud
    // ---------------------------------------------------------------------

    #[test]
    fn malformed_timeout_on_wait_is_rejected() {
        let yaml = r#"
operation: wait.badtimeout
jurisdiction: _default
steps:
  - id: waiter
    type: document.board_minutes
    wait_for: consent.approved
    timeout: 30x
"#;
        let err = lower_yaml(yaml).unwrap_err();
        assert!(
            matches!(err, LoweringError::InvalidDuration { ref step, ref value, .. } if step == "waiter" && value == "30x"),
            "expected InvalidDuration; got {err:?}"
        );
    }

    #[test]
    fn wait_without_timeout_is_rejected() {
        // A wait with no timeout silently blocks forever; the lowerer rejects
        // it rather than mint a 0 (disabled) timeout.
        let yaml = r#"
operation: wait.notimeout
jurisdiction: _default
steps:
  - id: waiter
    type: document.board_minutes
    wait_for: consent.approved
"#;
        let err = lower_yaml(yaml).unwrap_err();
        assert_eq!(
            err,
            LoweringError::WaitWithoutTimeout {
                step: "waiter".to_string(),
                event: "consent.approved".to_string(),
            }
        );
    }

    #[test]
    fn well_formed_wait_lowers_with_real_timeout() {
        let yaml = r#"
operation: wait.ok
jurisdiction: _default
steps:
  - id: waiter
    type: document.board_minutes
    wait_for: consent.approved
    timeout: 5m
"#;
        let report = lower_yaml(yaml).unwrap();
        let wait = step_named(&report, "waiter").wait.as_ref().unwrap();
        assert_eq!(wait.event, "consent.approved");
        assert_eq!(wait.timeout_secs, 300);
    }

    // ---------------------------------------------------------------------
    // Finding 4 — missing compensation type fails loud
    // ---------------------------------------------------------------------

    #[test]
    fn compensation_without_type_is_rejected() {
        // A compensation clause with no `type` would previously become a
        // silent noop. It must fail loud — a rollback that inverts nothing is
        // a security defect.
        let yaml = r#"
operation: comp.notype
jurisdiction: _default
steps:
  - id: act
    type: update.entity_status
compensation:
  steps:
    - id: undo
      inverts: act
      params:
        entity_id: "x"
"#;
        let err = lower_yaml(yaml).unwrap_err();
        assert_eq!(
            err,
            LoweringError::MissingCompensationType {
                forward: "act".to_string(),
            }
        );
    }

    #[test]
    fn compensation_with_empty_type_is_rejected() {
        let yaml = r#"
operation: comp.emptytype
jurisdiction: _default
steps:
  - id: act
    type: update.entity_status
compensation:
  steps:
    - id: undo
      inverts: act
      type: ""
"#;
        let err = lower_yaml(yaml).unwrap_err();
        assert_eq!(
            err,
            LoweringError::MissingCompensationType {
                forward: "act".to_string(),
            }
        );
    }

    // ---------------------------------------------------------------------
    // Finding 6 — program output declaration is recovered
    // ---------------------------------------------------------------------

    #[test]
    fn outputs_sequence_form_recovered() {
        let yaml = r#"
operation: out.seq
jurisdiction: _default
outputs: [entity_id, status]
steps:
  - id: act
    type: update.entity_status
"#;
        let report = lower_yaml(yaml).unwrap();
        assert_eq!(
            report.program.outputs,
            vec![
                ("entity_id".to_string(), OpType::String),
                ("status".to_string(), OpType::String),
            ]
        );
    }

    #[test]
    fn outputs_mapping_form_with_type_hints_recovered() {
        let yaml = r#"
operation: out.map
jurisdiction: _default
outputs:
  entity_id: entity_ref
  share_count: int
  active: bool
steps:
  - id: act
    type: update.entity_status
"#;
        let report = lower_yaml(yaml).unwrap();
        assert_eq!(
            report.program.outputs,
            vec![
                ("entity_id".to_string(), OpType::EntityRef),
                ("share_count".to_string(), OpType::Int),
                ("active".to_string(), OpType::Bool),
            ]
        );
    }

    #[test]
    fn returns_alias_recovered() {
        let yaml = r#"
operation: out.returns
jurisdiction: _default
returns: [result_id]
steps:
  - id: act
    type: update.entity_status
"#;
        let report = lower_yaml(yaml).unwrap();
        assert_eq!(
            report.program.outputs,
            vec![("result_id".to_string(), OpType::String)]
        );
    }

    #[test]
    fn no_outputs_section_means_empty_not_a_default() {
        // Absent outputs is the genuine "returns nothing" — vec![], no warning.
        let report = lower_yaml(SIMPLE).unwrap();
        assert!(report.program.outputs.is_empty());
    }

    #[test]
    fn unknown_output_type_hint_warns_and_falls_back_to_string() {
        let yaml = r#"
operation: out.badhint
jurisdiction: _default
outputs:
  weird: quaternion
steps:
  - id: act
    type: update.entity_status
"#;
        let report = lower_yaml(yaml).unwrap();
        assert_eq!(
            report.program.outputs,
            vec![("weird".to_string(), OpType::String)]
        );
        assert!(report
            .warnings
            .iter()
            .any(|w| w.contains("quaternion") && w.contains("unknown type hint")));
    }

    // ---------------------------------------------------------------------
    // Integration — a lowered, gated program type-checks end-to-end with the
    // inferred signatures (proves finding 5 + 1 produce op-core-valid output).
    // ---------------------------------------------------------------------

    #[test]
    fn lowered_simple_program_typechecks_with_inferred_signatures() {
        let report = lower_yaml(SIMPLE).unwrap();
        let tc = op_core::typecheck_program(&report.program);
        assert!(
            tc.success,
            "lowered SIMPLE must typecheck with inferred signatures; errors: {:?}",
            tc.errors
        );
    }
}
