//! Report canonical proof-bundle bytes per synthesized program size.
//!
//! Used to populate the B5 row of `docs/benchmarks.md`. The bundle
//! shape matches the `proof_bundle_determinism` integration test:
//! ordered `(step, primitive, args, outcome)` entries serialized via
//! `serde_json::to_vec` — a deterministic wire form over a
//! `BTreeMap`-backed arg structure.

use std::collections::BTreeMap;

use op_core::host::{HostOutcome, NoopHost, OpHost, PrimitiveCall};
use op_core::{
    Contracts, Effect, GasBudget, OpExpr, OpProgram, OpStep, OpType, Primitive, ProgramMetadata,
    Statement, StepBody, StepSignature,
};

#[derive(serde::Serialize)]
struct BundleEntry {
    step: String,
    primitive: String,
    args: BTreeMap<String, serde_json::Value>,
    outcome: serde_json::Value,
}

#[derive(serde::Serialize)]
struct ProofBundle {
    program: String,
    jurisdiction: String,
    entries: Vec<BundleEntry>,
}

fn reduce(e: &OpExpr) -> serde_json::Value {
    match e {
        OpExpr::String(s) => serde_json::Value::String(s.clone()),
        OpExpr::Int(i) => serde_json::Value::from(*i),
        OpExpr::Bool(b) => serde_json::Value::Bool(*b),
        _ => serde_json::Value::Null,
    }
}

fn execute_bundle(program: &OpProgram, host: &NoopHost) -> ProofBundle {
    let mut entries = Vec::new();
    for stmt in &program.body {
        let Statement::Step(step) = stmt else {
            continue;
        };
        let StepBody::Primitive(prim, args) = &step.body else {
            continue;
        };
        let reduced: BTreeMap<String, serde_json::Value> =
            args.iter().map(|(k, e)| (k.clone(), reduce(e))).collect();
        let call = PrimitiveCall {
            primitive: prim.clone(),
            args: reduced.clone(),
            jurisdiction: program.jurisdiction.clone(),
        };
        let outcome = match host.invoke(&call).unwrap() {
            HostOutcome::Completed(v) => v,
            HostOutcome::Waiting { event, .. } => serde_json::json!({ "waiting": event }),
        };
        entries.push(BundleEntry {
            step: step.id.clone(),
            primitive: prim.0.clone(),
            args: reduced,
            outcome,
        });
    }
    ProofBundle {
        program: program.name.clone(),
        jurisdiction: program.jurisdiction.clone(),
        entries,
    }
}

fn synthesize(n: usize) -> OpProgram {
    let mut body = Vec::with_capacity(n);
    body.push(Statement::Step(OpStep {
        id: "gate".to_string(),
        body: StepBody::Primitive(
            Primitive("screening.sanctions".to_string()),
            vec![(
                "subject_id".to_string(),
                OpExpr::String("entity-xyz".to_string()),
            )],
        ),
        signature: StepSignature {
            input: OpType::EntityRef,
            output: OpType::Bool,
            effects: vec![Effect::SanctionsCheck],
        },
        wait: None,
        on_failure: None,
        compensate: None,
        contracts: Contracts::default(),
    }));
    for i in 1..n {
        body.push(Statement::Step(OpStep {
            id: format!("step_{i}"),
            body: StepBody::Primitive(
                Primitive("update.entity_status".to_string()),
                vec![
                    (
                        "entity_id".to_string(),
                        OpExpr::String("entity-xyz".to_string()),
                    ),
                    ("status".to_string(), OpExpr::String("ACTIVE".to_string())),
                ],
            ),
            signature: StepSignature {
                input: OpType::Record(vec![
                    ("entity_id".to_string(), OpType::EntityRef),
                    ("status".to_string(), OpType::String),
                ]),
                output: OpType::Record(vec![("status".to_string(), OpType::String)]),
                effects: vec![Effect::SovereignWrite],
            },
            wait: None,
            on_failure: None,
            compensate: None,
            contracts: Contracts::default(),
        }));
    }
    OpProgram {
        name: format!("synth.{n}.op"),
        jurisdiction: "_default".to_string(),
        metadata: ProgramMetadata {
            version: "0.1.0".to_string(),
            description: format!("{n}-step program."),
        },
        inputs: vec![("entity_id".to_string(), OpType::EntityRef)],
        outputs: vec![("status".to_string(), OpType::String)],
        effects: vec![Effect::SanctionsCheck, Effect::SovereignWrite],
        participants: vec![],
        approval: None,
        contracts: Contracts::default(),
        body,
        gas_budget: GasBudget::default(),
    }
}

fn main() {
    let host = NoopHost;
    println!("steps,bytes");
    for n in [2usize, 16, 64, 256] {
        let program = synthesize(n);
        let bundle = execute_bundle(&program, &host);
        let bytes = serde_json::to_vec(&bundle).unwrap();
        println!("{n},{}", bytes.len());
    }
}
