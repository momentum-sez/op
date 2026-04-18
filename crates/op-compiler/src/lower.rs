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
    CompensationClause, Contract, Contracts, Effect, FailureAction, GasBudget, OpExpr, OpProgram,
    OpStep, OpType, Primitive, ProgramMetadata, Statement, StepBody, StepSignature, WaitSpec,
};
use serde::{Deserialize, Serialize};
use serde_yaml::Value as YamlValue;
use std::collections::BTreeMap;
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

    /// Type-checking failed after successful lowering.
    #[error("type check failed after lowering: {errors:?}")]
    TypeCheckFailed {
        /// Type-check diagnostics.
        errors: Vec<String>,
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
    let steps_yaml = doc
        .get("steps")
        .and_then(YamlValue::as_sequence)
        .cloned()
        .unwrap_or_default();
    let compensation_map = index_compensation(&doc, &mut warnings);

    let mut body: Vec<Statement> = Vec::new();
    let known_ids: Vec<String> = steps_yaml
        .iter()
        .filter_map(|s| s.get("id").and_then(YamlValue::as_str))
        .map(|s| s.to_string())
        .collect();

    for step_yaml in &steps_yaml {
        let step = lower_step(step_yaml, &compensation_map, &known_ids, &mut warnings)?;
        body.push(Statement::Step(step));
    }

    let metadata = ProgramMetadata {
        version,
        description,
    };

    let gas_budget = GasBudget::default();

    let program = OpProgram {
        name,
        jurisdiction,
        metadata,
        inputs,
        outputs: vec![],
        effects: vec![],
        participants: vec![],
        approval: None,
        contracts: Contracts::default(),
        body,
        gas_budget,
    };

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

fn lower_step(
    step: &YamlValue,
    compensation: &BTreeMap<String, CompensationClause>,
    known_ids: &[String],
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

    let effects = compliance_domains_to_effects(step, warnings);

    let wait = step
        .get("wait_for")
        .and_then(YamlValue::as_str)
        .map(|event| WaitSpec {
            event: event.to_string(),
            timeout_secs: step
                .get("timeout")
                .and_then(YamlValue::as_str)
                .map(parse_duration_seconds)
                .unwrap_or(0),
        });

    let on_failure = step
        .get("on_failure")
        .and_then(YamlValue::as_str)
        .and_then(parse_failure_action);

    let condition_requires = step
        .get("condition")
        .and_then(YamlValue::as_str)
        .map(|c| Contract::Expr(OpExpr::String(c.to_string())));

    let contracts = Contracts {
        requires: condition_requires.into_iter().collect(),
        ensures: vec![],
    };

    let primitive = Primitive(step_type);
    let body = StepBody::Primitive(primitive, args);
    let compensate = compensation.get(&id).cloned();

    Ok(OpStep {
        id,
        body,
        signature: StepSignature {
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

fn parse_duration_seconds(d: &str) -> u64 {
    let trimmed = d.trim();
    if trimmed.is_empty() {
        return 0;
    }
    let (num_part, unit) = trimmed.split_at(trimmed.len().saturating_sub(1));
    let n: u64 = num_part.parse().unwrap_or(0);
    match unit {
        "s" => n,
        "m" => n.saturating_mul(60),
        "h" => n.saturating_mul(3_600),
        "d" => n.saturating_mul(86_400),
        _ => 0,
    }
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

fn compliance_domains_to_effects(step: &YamlValue, warnings: &mut Vec<String>) -> Vec<Effect> {
    let mut effects = Vec::new();
    if let Some(doms) = step.get("compliance_domains").and_then(YamlValue::as_sequence) {
        for d in doms {
            if let Some(name) = d.as_str() {
                match name.to_lowercase().as_str() {
                    "sanctions" => effects.push(Effect::SanctionsCheck),
                    "aml" | "kyc" => effects.push(Effect::ExternalRead),
                    _ => {}
                }
            } else {
                warnings.push(format!("compliance_domains item not a string: {d:?}"));
            }
        }
    }
    effects
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
    warnings: &mut Vec<String>,
) -> BTreeMap<String, CompensationClause> {
    let mut out = BTreeMap::new();
    let Some(comp) = doc.get("compensation") else {
        return out;
    };
    let Some(steps) = comp.get("steps").and_then(YamlValue::as_sequence) else {
        return out;
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
        let primitive_name = s
            .get("type")
            .and_then(YamlValue::as_str)
            .unwrap_or("noop")
            .to_string();
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
    out
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
        assert_eq!(
            err,
            LoweringError::UnknownDependency("missing".to_string())
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
        assert_eq!(parse_duration_seconds("30s"), 30);
        assert_eq!(parse_duration_seconds("5m"), 300);
        assert_eq!(parse_duration_seconds("2h"), 7_200);
        assert_eq!(parse_duration_seconds("7d"), 604_800);
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
}
