//! Compilation-function microbenchmark `[[·]] : Lex -> Op`.
//!
//! B4 from the Op paper's empirical evaluation: end-to-end
//! `compile_lex` throughput on a workload of 100 admissible Lex terms
//! spanning the six compilation cases of §6.2:
//!
//! 1. constants (bool/int/string),
//! 2. prelude variables,
//! 3. pattern match,
//! 4. defeasible rule with one exception,
//! 5. sanctions-dominance,
//! 6. filled discretion hole.
//!
//! Each bench iteration compiles all 100 terms; `Throughput::Elements`
//! is set so Criterion reports per-term throughput (terms/sec).

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use op_lex_compiler::{
    compile_lex, CompileCtx, LexBranch, LexException, LexTerm, LexValue, Witness,
};

/// Build a 100-term workload mixing all six §6.2 compilation cases.
/// The mix is deterministic: 20 constants, 20 prelude vars, 15
/// matches, 15 defeasibles, 15 sanctions-dominance, 15 hole-fills.
fn build_workload() -> Vec<LexTerm> {
    let mut terms = Vec::with_capacity(100);

    // 20 constants across bool/int/string.
    for i in 0..10 {
        terms.push(LexTerm::const_int(i as i64));
    }
    for i in 0..5 {
        terms.push(LexTerm::const_bool(i % 2 == 0));
    }
    for i in 0..5 {
        terms.push(LexTerm::const_string(&format!("literal-{i}")));
    }

    // 20 prelude variable references (canonical prelude ships
    // `prelude.true` and `prelude.false` — we alternate).
    for i in 0..20 {
        let name = if i % 2 == 0 { "prelude.true" } else { "prelude.false" };
        terms.push(LexTerm::var(name, i as u32));
    }

    // 15 pattern matches on a two-branch variant scrutinee.
    for i in 0..15 {
        terms.push(LexTerm::Match {
            scrutinee: Box::new(LexTerm::Const(LexValue::Variant {
                tag: if i % 2 == 0 { "yes".to_string() } else { "no".to_string() },
                payload: Box::new(LexValue::Unit),
            })),
            branches: vec![
                LexBranch {
                    tag: "yes".to_string(),
                    binder: "_".to_string(),
                    body: LexTerm::const_bool(true),
                },
                LexBranch {
                    tag: "no".to_string(),
                    binder: "_".to_string(),
                    body: LexTerm::const_bool(false),
                },
            ],
        });
    }

    // 15 defeasibles with one exception each.
    for i in 0..15 {
        terms.push(LexTerm::Defeasible {
            name: format!("rule-{i}"),
            base: Box::new(LexTerm::const_bool(true)),
            exceptions: vec![LexException {
                guard: LexTerm::const_bool(false),
                body: LexTerm::const_bool(false),
                priority: 10,
                source_position: 0,
            }],
        });
    }

    // 15 sanctions-dominance nodes.
    for i in 0..15 {
        terms.push(LexTerm::sanctions_dominance_of(LexTerm::const_string(
            &format!("entity-{i}"),
        )));
    }

    // 15 filled discretion holes.
    for i in 0..15 {
        terms.push(LexTerm::HoleFill {
            hole_id: format!("h{i}"),
            value: Box::new(LexTerm::const_int(i as i64)),
            witness: Witness {
                authority: "ofac".to_string(),
                digest: format!("0x{i:02x}"),
                timestamp: "2026-04-18T10:00:00Z".to_string(),
            },
        });
    }

    assert_eq!(terms.len(), 100);
    terms
}

/// B4 — `compile_lex` throughput (terms/sec) over 100 admissible
/// terms.
fn bench_compile_lex(c: &mut Criterion) {
    let ctx = CompileCtx::with_canonical_prelude("bench.compile");
    let workload = build_workload();
    // Sanity check: every term in the workload is admissible and
    // compiles without error. Failure here would be a setup bug,
    // not a measurement.
    for (i, term) in workload.iter().enumerate() {
        compile_lex(term, &ctx).unwrap_or_else(|e| {
            panic!("workload[{i}] failed to compile: {e:?}")
        });
    }

    let mut group = c.benchmark_group("compile_lex");
    group.throughput(Throughput::Elements(workload.len() as u64));
    group.bench_function("100_admissible_terms", |b| {
        b.iter(|| {
            for term in &workload {
                let _ = compile_lex(term, &ctx).unwrap();
            }
        });
    });
    group.finish();
}

criterion_group!(benches, bench_compile_lex);
criterion_main!(benches);
