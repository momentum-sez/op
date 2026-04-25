# Empirical Evaluation

Microbenchmarks measuring five properties of the Op pipeline: type
checking, deterministic execution under a minimal host, effect-row
composition, Lex→Op compilation throughput, and proof-bundle size
together with Coq-checking time for the verdict-preservation
mechanization.

All measurements use Criterion 0.5 with 30 samples, a 1 s warm-up, and
a 3 s measurement window per data point. The Coq timing is a `time
coqc` invocation against `formal/coq/CompilationSoundness.v` with no
pre-existing `.vo` cache.

## Environment

| Field              | Value                                                   |
|--------------------|---------------------------------------------------------|
| Machine            | Apple M4 Max, 16 cores, 128 GB RAM                      |
| Operating system   | macOS 26.2 (Darwin 25.2.0 kernel)                       |
| Rust toolchain     | Repo pin: `rustc 1.86.0`; historical snapshot collected with `rustc 1.95.0-nightly (859951e3c 2026-02-24)` |
| Rocq / Coq         | Rocq Prover 9.1.1, compiled with OCaml 5.4.1            |
| Benchmark harness  | Criterion 0.5                                           |
| Workload seed      | Deterministic: fixed step IDs, fixed literal arguments  |

## Workload

Five synthetic workloads cover the pipeline end-to-end. All measured
programs typecheck successfully; all `sovereign_write` steps are
dominated by a leading `sanctions_check`.

| Name          | Shape                                                                 |
|---------------|----------------------------------------------------------------------|
| `hello`       | 2 steps — 1 sanctions gate + 1 `sovereign_write` (paper's example)   |
| `16` / `64` / `256` | 1 sanctions gate + (N-1) `sovereign_write` steps               |
| `N=4` variant | Shortest effect-row composition input                                 |
| 100 Lex terms | Mix across the six §6.2 cases: 20 constants, 20 prelude vars, 15 matches, 15 defeasibles (one exception each), 15 sanctions-dominance, 15 filled holes |

## Results

Criterion reports a three-value confidence interval `[low estimate high]`
around the median wall-clock time. The tables below quote the
`estimate` column (median) with `±` expressing the half-width of the
reported 95% confidence interval.

### B1 — `typecheck_program` wall time

| Steps  | Median time  | Confidence (± half-width) | Per-step cost |
|--------|--------------|---------------------------|---------------|
| 2 (hello) | 463 ns    | ± 2 ns                    | 231 ns        |
| 16     | 3.32 µs      | ± 21 ns                   | 208 ns        |
| 64     | 12.63 µs     | ± 53 ns                   | 197 ns        |
| 256    | 50.34 µs     | ± 306 ns                  | 197 ns        |

Per-step cost flattens around 200 ns for N ≥ 16; the 2-step
`hello-op` pays a fixed setup overhead. Empirical scaling is linear
in step count, matching the bidirectional-check shape: each step is
visited once, one linearity lookup, one effect union, one gas-table
lookup.

### B2 — Deterministic execution under `NoopHost`

Wall time for the end-to-end step walker from the paper's `hello-op`
example: reduce literal arguments, invoke the host, collect outcome
into a replay trace.

| Steps  | Median time  | Confidence (± half-width) | Per-step cost |
|--------|--------------|---------------------------|---------------|
| 2 (hello) | 716 ns    | ± 7 ns                    | 358 ns        |
| 16     | 5.84 µs      | ± 31 ns                   | 365 ns        |
| 64     | 23.60 µs     | ± 63 ns                   | 369 ns        |
| 256    | 94.84 µs     | ± 464 ns                  | 370 ns        |

Per-step cost is stable at ~370 ns across all sizes — consistent with
`O(N)` walker shape plus a fixed-cost JSON-reduction per primitive call. The
current structural gas table is construct-shaped (`step_cost = 10` by
default), not effect-specific; hosts may replace `StructuralCostTable` for
deployment economics.

### B3 — Effect-row composition (`program_effect_row`)

| Steps  | Median time   | Confidence (± half-width) | Throughput      |
|--------|---------------|---------------------------|-----------------|
| 4      | 30.8 ns       | ± 0.3 ns                  | 125 M steps/s   |
| 16     | 138 ns        | ± 1 ns                    | 116 M steps/s   |
| 64     | 648 ns        | ± 2 ns                    | 99 M steps/s    |
| 256    | 2.12 µs       | ± 0.04 ns (3 sig figs)    | 121 M steps/s   |

Effect-row composition processes ~100–125 M steps/sec. The union +
dedup pass is cache-resident for all tested sizes; throughput
stabilizes once the pass amortizes small-N overhead.

### B4 — `compile_lex` throughput

| Workload            | Median time (100 terms) | Confidence      | Per-term | Throughput     |
|---------------------|-------------------------|-----------------|----------|----------------|
| 100 admissible Lex terms | 47.9 µs            | ± 160 ns        | 479 ns   | 2.09 M terms/s |

Compilation across all six §6.2 cases averages under 500 ns per term.
The defeasible case is the most expensive per term (nested `Match`
emission with exception priority ordering); constants and prelude vars
dominate the fast end.

### B5 — Proof-bundle size + Coq-checking time

Canonical proof-bundle bytes measured by serializing the ordered
`(step, primitive, args, outcome)` entries via `serde_json::to_vec` —
the same wire form the `proof_bundle_determinism` test exercises.

| Program    | Bundle bytes | Bytes per step |
|------------|--------------|----------------|
| 2 steps    | 484          | 242            |
| 16 steps   | 3 711        | 232            |
| 64 steps   | 14 799       | 231            |
| 256 steps  | 59 308       | 232            |

Bundle cost is 230 B/step once fixed header overhead amortizes. The
shape is dominated by the replay trace, not the typed-signature
metadata.

Coq checking of the mechanized compilation-soundness lemma:

| Target                                 | Elapsed (`time coqc`)  |
|----------------------------------------|------------------------|
| `formal/coq/CompilationSoundness.v`    | 0.25 s (real), 0.20 s user, 0.04 s sys |

The verdict-preservation proof — including `verdict_preservation_sanctions`
and the `lift_value_emits_unique` lemma — checks in under a third of a
second from a cold `.vo` cache.

## Comparison to related systems

- **Catala** (ICFP 2021) — the Catala tax-rule compiler reports
  whole-corpus compilation in the low-seconds range for 1000-rule
  corpora. The Op Lex-to-Op compiler handles 100 admissible Lex terms in 48 µs, so a direct
  per-term scaling would be approximately 0.5 ms for 1000 terms
  (within a generous constant factor; corpora are not drawn from the
  same distribution, and Catala performs tax-specific desugaring Op
  does not).
- **WebAssembly deterministic execution** (PLDI 2017) — production
  WASM interpreters sit within a 1.5× envelope of native on tight
  loops. Op's deterministic-host walker processes ~370 ns per
  step on a workflow-shaped program. The Op evaluator is simpler than
  a WASM interpreter (single step dispatch, typed primitive calls, no
  control-flow decoding), so the comparison is structural: the same
  complexity order, dominated by host-call overhead rather than
  interpreter loop cost.

## Reproduction

```sh
cargo bench -p op-core --bench op_pipeline -- \
    --measurement-time 3 --warm-up-time 1 --sample-size 30
cargo bench -p op-lex-compiler --bench compile_lex -- \
    --measurement-time 3 --warm-up-time 1 --sample-size 30
cargo run --release -p op-core --example bundle-size
time coqc formal/coq/CompilationSoundness.v
```
