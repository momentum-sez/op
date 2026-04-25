//! Hello, Op — a 60-second tour of the language.
//!
//! Run:
//!     cargo run --example hello-op -p op-core
//!
//! What Op is: a typed effectful workflow language for multi-step economic
//! programs. Step composition is explicit, steps have typed inputs and
//! outputs, operational effects are tracked statically, compensation
//! attaches to the forward program it inverts, and proof obligations are
//! first-class constructs.
//!
//! Why Op matters: workflow configuration today hides language semantics
//! inside YAML — step composition in `depends_on` edges, variable binding
//! via string-path interpolation, failure policy as ad-hoc enums,
//! compensation detached from the step it inverts. These are language
//! jobs, performed in a format with no type system. Op makes them
//! language features.
//!
//! The tour below exercises the four load-bearing surfaces of op-core:
//!
//!   1. PARSE — an AST constructed programmatically (the serde derivation
//!      on `OpProgram` is equally the JSON wire format).
//!   2. TYPECHECK — bidirectional check over `Gamma |- e : T ! E`, with
//!      effect-safety: any `sovereign_write`, `identity_mutation`, or
//!      `fiscal_transfer` must be dominated by a `sanctions_check`.
//!   3. EXECUTE — every primitive flows through `OpHost`. The example
//!      uses `NoopHost` (echoes the call as a deterministic JSON record);
//!      a sovereign kernel plugs in production semantics through the
//!      same trait.
//!   4. REPORT — a compliance-carrying verdict: program digest, composed
//!      effect row, structural gas bill, trace of host outcomes. The
//!      shape of a replayable proof bundle.
//!
//! The program modeled here is the smallest workflow that shows all four
//! surfaces: screen an entity against sanctions, then activate it. The
//! activation is a `sovereign_write`; the screen supplies the dominating
//! `sanctions_check`. Strip the gate and `typecheck_program` rejects
//! the program before any primitive runs.

use op_core::host::{HostOutcome, NoopHost, OpHost, PrimitiveCall};
use op_core::{
    program_effect_row, typecheck_program, Contracts, Effect, GasBudget, OpExpr, OpProgram, OpStep,
    OpType, Primitive, ProgramMetadata, Statement, StepBody, StepSignature,
};
use std::collections::BTreeMap;

fn main() {
    // 1. PARSE. The AST built below is what `parse_program` would produce
    //    from the equivalent JSON wire form. Authoring through the Rust
    //    constructors makes the typing obvious; authoring through JSON is
    //    the integration path a host runtime takes.
    let program = build_program();
    println!(
        "program      : {}  (jurisdiction: {})",
        program.name, program.jurisdiction
    );

    // 2. TYPECHECK. The checker composes effect rows across steps and
    //    enforces the sanctions-dominance rule. Undominated writes are
    //    rejected at compile time, before any primitive is invoked.
    let check = typecheck_program(&program);
    if !check.success {
        eprintln!("typecheck FAILED: {:#?}", check.errors);
        std::process::exit(1);
    }
    let composed: Vec<Effect> = program_effect_row(&program);
    let gas = check.gas_analysis.as_ref().expect("gas analysis present");
    println!("typecheck    : OK  (composed effects: {composed:?})");
    println!("gas bound    : {} structural units", gas.structural_bound);

    // 3. EXECUTE. Walk the steps in source order; fulfill each primitive
    //    through the host. A deliberately tiny reference evaluator — one
    //    line per step — sufficient to show the single seam every host
    //    plugs into. Same program + same inputs + same host → same trace
    //    on every replay.
    let host = NoopHost;
    let mut trace: Vec<(String, HostOutcome)> = Vec::new();
    for stmt in &program.body {
        if let Statement::Step(step) = stmt {
            if let StepBody::Primitive(prim, args) = &step.body {
                let call = PrimitiveCall {
                    primitive: prim.clone(),
                    args: reduce_args(args),
                    jurisdiction: program.jurisdiction.clone(),
                };
                let outcome = host.invoke(&call).expect("host must succeed");
                println!(
                    "step {:<10}: {} -> {}",
                    step.id,
                    prim.0,
                    summarize(&outcome)
                );
                trace.push((step.id.clone(), outcome));
            }
        }
    }

    // 4. REPORT. Every step that fired, the composed effect row it
    //    satisfied, the gas it billed. A host that emits signed proof
    //    bundles (SAVM, Coq-extracted interpreter, zkVM) stamps the
    //    same shape with an attestation.
    println!(
        "verdict      : ADMIT  ({} steps executed, trace is replayable)",
        trace.len()
    );
}

// The smallest program that shows the sanctions-dominance rule: a screen
// followed by a state mutation, with effects declared on every step.
fn build_program() -> OpProgram {
    OpProgram {
        name: "hello.op".to_string(),
        jurisdiction: "_default".to_string(),
        metadata: ProgramMetadata {
            version: "0.1.0".to_string(),
            description: "Screen and activate an entity.".to_string(),
        },
        inputs: vec![("entity_id".to_string(), OpType::EntityRef)],
        outputs: vec![("status".to_string(), OpType::String)],
        effects: vec![Effect::SanctionsCheck, Effect::SovereignWrite],
        participants: vec![],
        approval: None,
        contracts: Contracts::default(),
        body: vec![
            Statement::Step(OpStep {
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
            }),
            Statement::Step(OpStep {
                id: "activate".to_string(),
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
            }),
        ],
        gas_budget: GasBudget::default(),
    }
}

// Reduce an Op argument list to the JSON value map the host expects. A
// full evaluator traverses `OpExpr`; the tour keeps to literals.
fn reduce_args(args: &[(String, OpExpr)]) -> BTreeMap<String, serde_json::Value> {
    let mut out = BTreeMap::new();
    for (name, expr) in args {
        let value = match expr {
            OpExpr::String(s) => serde_json::Value::String(s.clone()),
            OpExpr::Int(i) => serde_json::Value::Number((*i).into()),
            OpExpr::Bool(b) => serde_json::Value::Bool(*b),
            _ => serde_json::Value::Null,
        };
        out.insert(name.clone(), value);
    }
    out
}

fn summarize(outcome: &HostOutcome) -> String {
    match outcome {
        HostOutcome::Completed(_) => "COMPLETED".to_string(),
        HostOutcome::Waiting { event, .. } => format!("WAITING on {event}"),
    }
}
