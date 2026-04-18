//! Op pipeline microbenchmarks.
//!
//! Five metrics over synthesized workloads:
//!
//! * **B1 typecheck cost** — `typecheck_program` wall time on the hello-op
//!   program and on 16/64/256-step synthesized programs.
//! * **B2 deterministic execution cost** — `NoopHost`-driven end-to-end
//!   walk of the same programs, measuring wall time to completion plus
//!   the structural gas bill the checker emitted.
//! * **B3 effect-row composition** — `program_effect_row` over N-step
//!   programs for N ∈ {4, 16, 64, 256}.
//! * **B4 proof-bundle size** — canonical bytes per synthesized program,
//!   reported alongside the bench in `docs/benchmarks.md`.
//!
//! The synthesized programs share one shape: a single sanctions gate at
//! the head, followed by N-1 `update.entity_status` `sovereign_write`
//! steps. Each step's effects compose into the program-level row, each
//! `sovereign_write` is dominated by the leading `sanctions_check`.

use std::collections::BTreeMap;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use op_core::host::{HostOutcome, NoopHost, OpHost, PrimitiveCall};
use op_core::{
    program_effect_row, typecheck_program, Contracts, Effect, GasBudget, OpExpr, OpProgram,
    OpStep, OpType, Primitive, ProgramMetadata, Statement, StepBody, StepSignature,
};

/// Build the smallest well-typed program: sanctions gate + one
/// sovereign_write. Matches the `hello-op` example shape — the
/// language paper's canonical 60-second tour program.
fn hello_op_program() -> OpProgram {
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
        body: vec![gate_step(), write_step("activate")],
        gas_budget: GasBudget::default(),
    }
}

/// Synthesize an N-step program: one gate + (N-1) sovereign_write steps.
/// All sovereign writes are dominated by the leading gate, so the
/// effect-safety rule is satisfied.
fn synthesize_program(n_steps: usize) -> OpProgram {
    assert!(n_steps >= 1, "N must be at least 1");
    let mut body: Vec<Statement> = Vec::with_capacity(n_steps);
    body.push(gate_step());
    for i in 1..n_steps {
        body.push(write_step(&format!("step_{i}")));
    }
    OpProgram {
        name: format!("synth.{n_steps}.op"),
        jurisdiction: "_default".to_string(),
        metadata: ProgramMetadata {
            version: "0.1.0".to_string(),
            description: format!("Synthesized {n_steps}-step program."),
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

fn gate_step() -> Statement {
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
    })
}

fn write_step(id: &str) -> Statement {
    Statement::Step(OpStep {
        id: id.to_string(),
        body: StepBody::Primitive(
            Primitive("update.entity_status".to_string()),
            vec![
                ("entity_id".to_string(), OpExpr::String("entity-xyz".to_string())),
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
    })
}

/// Reduce literal argument expressions to JSON. Matches the
/// `hello-op` reducer shape — expressions carrying only literals.
fn reduce_args(args: &[(String, OpExpr)]) -> BTreeMap<String, serde_json::Value> {
    let mut out = BTreeMap::new();
    for (name, expr) in args {
        let v = match expr {
            OpExpr::String(s) => serde_json::Value::String(s.clone()),
            OpExpr::Int(i) => serde_json::Value::from(*i),
            OpExpr::Bool(b) => serde_json::Value::Bool(*b),
            _ => serde_json::Value::Null,
        };
        out.insert(name.clone(), v);
    }
    out
}

/// Walk a program through a host, returning the count of steps
/// whose primitive invocation completed. This is the minimum-
/// complexity executor the `hello-op` example demonstrates.
fn execute(program: &OpProgram, host: &NoopHost) -> usize {
    let mut count = 0usize;
    for stmt in &program.body {
        let Statement::Step(step) = stmt else { continue };
        let StepBody::Primitive(prim, args) = &step.body else { continue };
        let call = PrimitiveCall {
            primitive: prim.clone(),
            args: reduce_args(args),
            jurisdiction: program.jurisdiction.clone(),
        };
        let outcome = host.invoke(&call).expect("noop host succeeds");
        if matches!(outcome, HostOutcome::Completed(_)) {
            count += 1;
        }
    }
    count
}

/// B1 — typecheck cost on hello-op + synthesized programs.
fn bench_typecheck(c: &mut Criterion) {
    let mut group = c.benchmark_group("typecheck");
    let hello = hello_op_program();
    group.throughput(Throughput::Elements(hello.body.len() as u64));
    group.bench_with_input(BenchmarkId::new("steps", "hello"), &hello, |b, p| {
        b.iter(|| {
            let result = typecheck_program(p);
            assert!(result.success);
        });
    });
    for n in [16usize, 64, 256] {
        let program = synthesize_program(n);
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::new("steps", n), &program, |b, p| {
            b.iter(|| {
                let result = typecheck_program(p);
                assert!(result.success);
            });
        });
    }
    group.finish();
}

/// B2 — deterministic execution cost under `NoopHost`.
fn bench_execute(c: &mut Criterion) {
    let mut group = c.benchmark_group("execute_noop");
    let host = NoopHost;
    let hello = hello_op_program();
    group.throughput(Throughput::Elements(hello.body.len() as u64));
    group.bench_with_input(BenchmarkId::new("steps", "hello"), &hello, |b, p| {
        b.iter(|| {
            let executed = execute(p, &host);
            assert_eq!(executed, p.body.len());
        });
    });
    for n in [16usize, 64, 256] {
        let program = synthesize_program(n);
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::new("steps", n), &program, |b, p| {
            b.iter(|| {
                let executed = execute(p, &host);
                assert_eq!(executed, p.body.len());
            });
        });
    }
    group.finish();
}

/// B3 — effect-row composition over N-step programs.
fn bench_effect_row(c: &mut Criterion) {
    let mut group = c.benchmark_group("effect_row");
    for n in [4usize, 16, 64, 256] {
        let program = synthesize_program(n);
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::new("steps", n), &program, |b, p| {
            b.iter(|| {
                let row = program_effect_row(p);
                // The composed row deduplicates: expect two entries —
                // SanctionsCheck (from the gate) + SovereignWrite (from
                // the writers). Assertion doubles as a sanity check
                // that the benchmarked code path ran.
                assert_eq!(row.len(), 2);
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_typecheck, bench_execute, bench_effect_row);
criterion_main!(benches);
