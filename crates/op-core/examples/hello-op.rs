//! Minimum-viable Op embedding.
//!
//! Build and run:
//!
//! ```bash
//! cargo run --example hello-op
//! ```
//!
//! The example constructs a tiny Op program programmatically, type-checks it,
//! and invokes its primitive through the built-in `NoopHost`. It exercises
//! the public surface of `op-core` without any kernel-side binding.

use op_core::host::{HostOutcome, NoopHost, OpHost, PrimitiveCall};
use op_core::{
    typecheck_program, Contracts, Effect, GasBudget, OpExpr, OpProgram, OpStep, OpType, Primitive,
    ProgramMetadata, Statement, StepBody, StepSignature,
};
use std::collections::BTreeMap;

fn main() {
    // Build a program: a trivial two-step pipeline — a sanctions gate
    // followed by an entity activation.
    let program = OpProgram {
        name: "hello.op".to_string(),
        jurisdiction: "_default".to_string(),
        metadata: ProgramMetadata {
            version: "0.1.0".to_string(),
            description: "Hello, Op.".to_string(),
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
                        OpExpr::Var("entity_id".to_string()),
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
                            OpExpr::Var("entity_id".to_string()),
                        ),
                        ("status".to_string(), OpExpr::String("ACTIVE".to_string())),
                    ],
                ),
                signature: StepSignature {
                    input: OpType::Record(vec![
                        ("entity_id".to_string(), OpType::EntityRef),
                        ("status".to_string(), OpType::String),
                    ]),
                    output: OpType::Record(vec![(
                        "status".to_string(),
                        OpType::String,
                    )]),
                    effects: vec![Effect::SovereignWrite],
                },
                wait: None,
                on_failure: None,
                compensate: None,
                contracts: Contracts::default(),
            }),
            Statement::Return(OpExpr::Var("activate".to_string())),
        ],
        gas_budget: GasBudget::default(),
    };

    let tc = typecheck_program(&program);
    if !tc.success {
        eprintln!("type-check failed: {:#?}", tc.errors);
        std::process::exit(1);
    }
    println!("program '{}' type-checks cleanly", program.name);

    // Invoke the first step's primitive through the NoopHost. In a real
    // deployment, the host would execute the primitive against a sovereign
    // kernel or backend of choice.
    let host = NoopHost;
    let mut args = BTreeMap::new();
    args.insert(
        "subject_id".to_string(),
        serde_json::Value::String("entity-xyz".to_string()),
    );
    let call = PrimitiveCall {
        primitive: Primitive("screening.sanctions".to_string()),
        args,
        jurisdiction: program.jurisdiction.clone(),
    };
    match host.invoke(&call).expect("host must succeed") {
        HostOutcome::Completed(v) => println!("host completed: {v}"),
        HostOutcome::Waiting { event, resume_token } => {
            println!("host suspended on {event} (token {resume_token})");
        }
    }
}
