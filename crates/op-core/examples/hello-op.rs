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
//! The tour below exercises the load-bearing surfaces of op-core. The
//! first two are the real language layer; the second two are an
//! ILLUSTRATIVE reference walk, not production execution:
//!
//!   1. PARSE — an AST constructed programmatically (the serde derivation
//!      on `OpProgram` is equally the JSON wire format).
//!   2. TYPECHECK — bidirectional check over `Gamma |- e : T ! E`, with
//!      effect-safety: any `sovereign_write`, `identity_mutation`, or
//!      `fiscal_transfer` must be dominated by a `sanctions_check`.
//!   3. WALK (illustrative) — visit each primitive through `OpHost`. The
//!      example uses `NoopHost`, which echoes the call as a deterministic
//!      JSON record. This is a tiny reference evaluator: it is NOT
//!      gas-metered, it enforces no compliance semantics, and it does not
//!      perform the sovereign mutation a real host would. A production
//!      host plugs in its own real semantics behind the same `OpHost`
//!      trait — the trait is the seam; the production behaviour lives
//!      out-of-tree.
//!   4. SUMMARIZE (illustrative) — print the program digest surrogate,
//!      composed effect row, static structural gas BOUND (computed at
//!      type-check, not charged here), and the trace of `NoopHost`
//!      outcomes. This is a worked illustration of the data a real
//!      proof bundle would carry, not a signed or replayable proof.
//!
//! The program modeled here is the smallest workflow that shows the
//! sanctions-dominance rule: screen an entity against sanctions, then
//! activate it. The activation is a `sovereign_write`; the screen
//! supplies the dominating `sanctions_check`. Strip the gate and
//! `typecheck_program` rejects the program before the walk begins.

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

    // 3. WALK (illustrative). Visit the steps in source order; fulfill
    //    each primitive through the host. This is a deliberately tiny
    //    reference evaluator — one line per step — sufficient only to show
    //    the single seam every host plugs into. It is NOT gas-metered, it
    //    applies no compliance semantics, and `NoopHost` performs no real
    //    sovereign mutation. A production host supplies real semantics
    //    behind the same trait. Same program + same inputs + same host →
    //    same trace, because `NoopHost` is deterministic.
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

    // 4. SUMMARIZE (illustrative). Every step the walk visited and the
    //    composed effect row the program declared. The gas figure printed
    //    above is the STATIC structural bound from type-check, not gas
    //    charged during this walk — no gas is metered here. A production
    //    host that emits signed proof bundles (e.g. a settlement VM, a
    //    Coq-extracted interpreter, a zkVM) would carry this shape AND an
    //    attestation; this example carries neither, so the line below is
    //    a walk summary, not an admissibility verdict or a replayable proof.
    println!(
        "walk summary : type-checked + {} steps visited via NoopHost \
         (illustrative; not gas-metered, not a signed proof)",
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
        // The program-level effect row must be the UNION of every step's
        // canonical effects. `screening.sanctions` carries `SanctionsCheck`
        // AND `ExternalRead` (it reads an external list), so both must be
        // declared here or `typecheck_program` rejects the program for an
        // under-declared effect row — exactly the check this example shows.
        effects: vec![
            Effect::SanctionsCheck,
            Effect::ExternalRead,
            Effect::SovereignWrite,
        ],
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
            // The program declares output `status: String`, so it must
            // `return` a `String`-typed value. The `activate` step binds its
            // id to its output type `Record([("status", String)])`; project
            // the `status` field to produce the declared `String` output.
            // (A declared non-Unit output with no matching return is itself a
            // type error this example would otherwise trip.)
            Statement::Return(OpExpr::Field(
                Box::new(OpExpr::Var("activate".to_string())),
                "status".to_string(),
            )),
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The example's honest-runnable contract: `build_program()` actually
    /// type-checks. WHY: this file's doc comments claim the tour reaches the
    /// WALK/SUMMARIZE steps "before the walk begins" only if typecheck passes;
    /// a program that fails its own typecheck would `exit(1)` and never
    /// demonstrate what the comments describe (the false-ad regression this
    /// closes). It also pins the two defects that previously broke it: a
    /// missing `return` for the declared `String` output, and an
    /// under-declared effect row missing `ExternalRead` from
    /// `screening.sanctions`.
    #[test]
    fn example_program_typechecks() {
        let program = build_program();
        let check = typecheck_program(&program);
        assert!(
            check.success,
            "hello-op example must type-check so the tour is honestly runnable; errors: {:?}",
            check.errors
        );
        // The composed effect row includes ExternalRead (from
        // screening.sanctions) — proving the declaration is the real union.
        let composed = program_effect_row(&program);
        assert!(
            composed.contains(&Effect::ExternalRead),
            "screening.sanctions contributes ExternalRead to the composed row, got {composed:?}"
        );
        // The gas figure the example prints is the STATIC structural bound,
        // present on the analysis — not gas charged during the walk.
        assert!(check.gas_analysis.is_some());
    }
}
