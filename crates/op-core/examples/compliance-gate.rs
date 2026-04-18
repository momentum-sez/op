//! Compliance gate — a one-screen demonstration of Op's verdict shape.
//!
//! Run:
//!     cargo run --example compliance-gate -p op-core
//!
//! What this shows: a tiny policy — "deny if the counterparty's
//! jurisdiction is on the sanctions list AND the transfer amount exceeds
//! the declared threshold" — encoded as an Op program and executed
//! against a rule-aware host. The verdict that comes out the other side
//! is the shape of an Op proof certificate:
//!
//!   - a content-addressed program digest (what was executed),
//!   - the composed effect row (what it was allowed to touch),
//!   - a structural gas bill (what the workflow skeleton cost),
//!   - a deterministic outcome trace (what the host returned, step by
//!     step),
//!   - a rendered admit / deny verdict.
//!
//! The check runs twice: once against a clean jurisdiction at a small
//! amount (ADMIT), once against a sanctioned jurisdiction at an amount
//! above the threshold (DENY). Same program, different inputs, fully
//! deterministic replay.

use op_core::host::{HostError, HostOutcome, OpHost, PrimitiveCall};
use op_core::{
    program_effect_row, typecheck_program, Contracts, Effect, GasBudget, OpExpr, OpProgram,
    OpStep, OpType, Primitive, ProgramMetadata, Statement, StepBody, StepSignature,
};
use serde_json::{json, Value};
use std::collections::BTreeMap;

/// The compliance rule.
///
/// Expressed in plain English: allow the transfer only if the
/// counterparty jurisdiction is not on the sanctions list, OR the
/// transfer amount is below the low-value threshold.
const SANCTIONED_JURISDICTIONS: &[&str] = &["kp", "ir", "ru-crimea"];
const LOW_VALUE_THRESHOLD_MINOR_UNITS: i64 = 10_000; // e.g., USD 100.00

fn main() {
    // 1. The program.  A two-step Op workflow: screen the counterparty
    //    jurisdiction, then evaluate the low-value threshold. Both are
    //    reads, bounded-side-effect; the downstream sovereign write is
    //    the authorize step, which carries the `sanctions_check` effect
    //    from the screen (effect safety is therefore satisfied by shape).
    let program = build_program();

    // 2. Typecheck — the same typecheck every host runs.
    let check = typecheck_program(&program);
    if !check.success {
        eprintln!("typecheck FAILED: {:#?}", check.errors);
        std::process::exit(1);
    }

    // 3. Content address the program.
    let digest = program_digest(&program);

    // 4. Two scenarios. Each drives the host with a different input.
    //    The host embeds the compliance rule; Op carries the scaffolding.
    let scenarios = [
        ("admit", "sg", 5_000),     // Singapore, USD 50.00 — well below threshold, clean list
        ("deny", "kp", 50_000_000), // sanctioned jurisdiction, USD 500,000 — rule denies
    ];

    for (label, jurisdiction, amount) in scenarios {
        println!("--- scenario: {label} ---");
        println!("inputs          : counterparty_jurisdiction = {jurisdiction}, amount = {amount}");
        let host = RuleHost::new(jurisdiction, amount);
        let verdict = execute(&program, &host);
        render_certificate(&program, &digest, &check, &verdict);
        println!();
    }
}

/// The executed trace: verdict + per-step outcomes.
struct ExecutionVerdict {
    admit: bool,
    outcomes: Vec<(String, HostOutcome)>,
    reason: String,
}

fn execute(program: &OpProgram, host: &RuleHost) -> ExecutionVerdict {
    let mut outcomes: Vec<(String, HostOutcome)> = Vec::new();
    let mut admit = true;
    let mut reason = String::from("all gates passed");
    for stmt in &program.body {
        let Statement::Step(step) = stmt else { continue };
        let StepBody::Primitive(prim, args) = &step.body else {
            continue;
        };
        let call = PrimitiveCall {
            primitive: prim.clone(),
            args: reduce_args(args),
            jurisdiction: program.jurisdiction.clone(),
        };
        match host.invoke(&call) {
            Ok(outcome) => {
                // A completed Bool primitive carries admit / deny.
                if let HostOutcome::Completed(Value::Bool(false)) = &outcome {
                    admit = false;
                    reason = format!("step '{}' evaluated to deny", step.id);
                }
                outcomes.push((step.id.clone(), outcome));
            }
            Err(HostError::PolicyRejection(msg)) => {
                admit = false;
                reason = msg.clone();
                outcomes.push((
                    step.id.clone(),
                    HostOutcome::Completed(Value::String(format!("rejected: {msg}"))),
                ));
                break;
            }
            Err(e) => {
                admit = false;
                reason = format!("host error: {e}");
                break;
            }
        }
    }
    ExecutionVerdict { admit, outcomes, reason }
}

/// The proof-certificate shape Op produces. A production host emits the
/// same fields plus a cryptographic signature and an append-only ledger
/// coordinate; the language-level shape is what you see here.
fn render_certificate(
    program: &OpProgram,
    digest: &str,
    check: &op_core::TypeCheckResult,
    verdict: &ExecutionVerdict,
) {
    println!("program digest  : {digest}");
    println!("composed effects: {:?}", program_effect_row(program));
    println!(
        "gas (structural): {} units",
        check.gas_analysis.as_ref().map(|g| g.structural_bound).unwrap_or(0)
    );
    println!("trace           :");
    for (id, outcome) in &verdict.outcomes {
        let summary = match outcome {
            HostOutcome::Completed(v) => format!("completed {v}"),
            HostOutcome::Waiting { event, .. } => format!("waiting on {event}"),
        };
        println!("  - {id}: {summary}");
    }
    let verdict_label = if verdict.admit { "ADMIT" } else { "DENY" };
    println!("verdict         : {verdict_label}  ({})", verdict.reason);
}

/// The program: a jurisdiction screen followed by a low-value check.
/// The `screening.sanctions` step carries the sanctions-check effect that
/// dominates the downstream writes (there are no writes in this demo —
/// the workflow is a pure admission gate — but the same shape extends
/// to write-bearing flows without changing the typechecker's reasoning).
fn build_program() -> OpProgram {
    let screen = OpStep {
        id: "screen".to_string(),
        body: StepBody::Primitive(
            Primitive("screening.sanctions".to_string()),
            vec![(
                "subject_jurisdiction".to_string(),
                OpExpr::Var("counterparty_jurisdiction".to_string()),
            )],
        ),
        signature: StepSignature {
            input: OpType::JurisdictionRef,
            output: OpType::Bool,
            effects: vec![Effect::SanctionsCheck, Effect::ExternalRead],
        },
        wait: None,
        on_failure: None,
        compensate: None,
        contracts: Contracts::default(),
    };
    let threshold = OpStep {
        id: "threshold".to_string(),
        body: StepBody::Primitive(
            Primitive("fiscal.threshold_check".to_string()),
            vec![
                ("amount".to_string(), OpExpr::Var("amount".to_string())),
                ("threshold".to_string(), OpExpr::Int(LOW_VALUE_THRESHOLD_MINOR_UNITS)),
            ],
        ),
        signature: StepSignature {
            input: OpType::Record(vec![
                ("amount".to_string(), OpType::Int),
                ("threshold".to_string(), OpType::Int),
            ]),
            output: OpType::Bool,
            effects: vec![Effect::Pure],
        },
        wait: None,
        on_failure: None,
        compensate: None,
        contracts: Contracts::default(),
    };

    OpProgram {
        name: "compliance.gate".to_string(),
        jurisdiction: "_default".to_string(),
        metadata: ProgramMetadata {
            version: "0.1.0".to_string(),
            description: "Deny if counterparty jurisdiction is sanctioned and amount exceeds threshold.".to_string(),
        },
        inputs: vec![
            ("counterparty_jurisdiction".to_string(), OpType::JurisdictionRef),
            ("amount".to_string(), OpType::Int),
        ],
        outputs: vec![("admit".to_string(), OpType::Bool)],
        effects: vec![Effect::SanctionsCheck, Effect::ExternalRead],
        participants: vec![],
        approval: None,
        contracts: Contracts::default(),
        body: vec![Statement::Step(screen), Statement::Step(threshold)],
        gas_budget: GasBudget::default(),
    }
}

/// A rule-aware host. The compliance policy lives here; Op carries the
/// scaffolding (typing, effect safety, gas, replay). That separation is
/// the point: the language is policy-neutral.
struct RuleHost {
    counterparty_jurisdiction: String,
    amount: i64,
}

impl RuleHost {
    fn new(jurisdiction: &str, amount: i64) -> Self {
        Self {
            counterparty_jurisdiction: jurisdiction.to_string(),
            amount,
        }
    }
}

impl OpHost for RuleHost {
    fn invoke(&self, call: &PrimitiveCall) -> Result<HostOutcome, HostError> {
        match call.primitive.0.as_str() {
            "screening.sanctions" => {
                // Admit unless the jurisdiction is on the sanctions list.
                let sanctioned = SANCTIONED_JURISDICTIONS
                    .contains(&self.counterparty_jurisdiction.as_str());
                // Policy rule: jurisdiction on the list + amount over
                // threshold → deny outright.
                if sanctioned && self.amount > LOW_VALUE_THRESHOLD_MINOR_UNITS {
                    return Err(HostError::PolicyRejection(format!(
                        "counterparty jurisdiction '{}' is sanctioned and amount {} exceeds \
                         threshold {}",
                        self.counterparty_jurisdiction, self.amount, LOW_VALUE_THRESHOLD_MINOR_UNITS
                    )));
                }
                Ok(HostOutcome::Completed(json!(!sanctioned)))
            }
            "fiscal.threshold_check" => {
                // Admit only when amount is below the threshold.
                Ok(HostOutcome::Completed(json!(self.amount <= LOW_VALUE_THRESHOLD_MINOR_UNITS)))
            }
            other => Err(HostError::UnknownPrimitive(other.to_string())),
        }
    }
}

fn reduce_args(args: &[(String, OpExpr)]) -> BTreeMap<String, Value> {
    let mut out = BTreeMap::new();
    for (name, expr) in args {
        let value = match expr {
            OpExpr::String(s) => Value::String(s.clone()),
            OpExpr::Int(i) => Value::Number((*i).into()),
            OpExpr::Bool(b) => Value::Bool(*b),
            _ => Value::Null,
        };
        out.insert(name.clone(), value);
    }
    out
}

/// A small content address over the program's serialized shape. The
/// production pipeline uses a stronger hash (BLAKE3 / SHA-256); this
/// crate stays dependency-light with a stable, deterministic FNV-1a
/// variant that is adequate for replay verification in a test context.
fn program_digest(program: &OpProgram) -> String {
    let canonical = serde_json::to_string(program).unwrap_or_default();
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in canonical.bytes() {
        h ^= byte as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01B3);
    }
    format!("fnv1a-64:{h:016x}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admit_small_amount_clean_jurisdiction() {
        let program = build_program();
        let check = typecheck_program(&program);
        assert!(check.success);
        let host = RuleHost::new("sg", 5_000);
        let verdict = execute(&program, &host);
        assert!(verdict.admit);
    }

    #[test]
    fn deny_sanctioned_jurisdiction_over_threshold() {
        let program = build_program();
        let host = RuleHost::new("kp", 50_000_000);
        let verdict = execute(&program, &host);
        assert!(!verdict.admit);
    }

    #[test]
    fn digest_is_deterministic() {
        let program = build_program();
        assert_eq!(program_digest(&program), program_digest(&program));
    }
}
