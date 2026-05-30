# Reproducibility

This document specifies the exact procedure for reproducing every executable
claim in this repository. A reviewer with the listed hardware and toolchain
should obtain bit-identical or functionally-identical results.

## Repository

- URL: <https://github.com/momentum-sez/op>
- Branch: `main`
- License: Apache-2.0 (`LICENSE`)

## Clone

```
git clone https://github.com/momentum-sez/op.git
cd op
```

The workspace is self-contained. No sibling checkouts, environment variables,
or private dependencies are required.

## Toolchain

Rust toolchain is pinned by `rust-toolchain.toml` at the repository root:

- Channel: `1.86.0` (stable)
- Components: `rustfmt`, `clippy`
- Profile: `minimal`

`rustup` honors this file automatically. The workspace MSRV declared in
`Cargo.toml` is `1.76`; the pin sits above MSRV. The pin is `1.86.0`
because several transitive dependencies (notably `hashbrown 0.17` via
`indexmap 2.14`) require Rust `edition2024`, stabilized in `1.85.0`.

Coq mechanization is checked against:

- Rocq Prover `9.1.1` (or compatible `9.x` — the container image
  `rocq/rocq:9.1` is used by CI).

## Expected results

### Rust workspace

```
cargo test --workspace
```

Expected: `97` tests pass across the four crates `op-core`, `op-compiler`,
`op-stdlib`, `op-lex-compiler`. Zero failures. Doc-tests contribute one
`ignored` entry from `op_lex_compiler` (signature-only).

Integration test binaries include `compensation_runtime`, `meet_monotonicity`,
`proof_bundle_determinism` (op-core); `golden_defeasible_tolling`,
`golden_flat_fsmr`, `golden_sanctions` (op-lex-compiler). Exact per-crate
counts can drift as the test suite grows; `cargo test --workspace` prints
the running totals.

### Clippy and rustfmt

```
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all -- --check
```

Expected: both exit `0` with no output.

### Hello-op example

```
cargo run --example hello-op -p op-core
```

Expected output (order and formatting are stable):

```
program      : hello.op  (jurisdiction: _default)
typecheck    : OK  (composed effects: [SovereignWrite, SanctionsCheck])
gas bound    : 20 structural units
step gate      : screening.sanctions -> COMPLETED
step activate  : update.entity_status -> COMPLETED
verdict      : ADMIT  (2 steps executed, trace is replayable)
```

The example source is `crates/op-core/examples/hello-op.rs`.

### Coq mechanization

```
cd formal/coq
make
```

The default `Makefile` target invokes `coq_makefile -f _CoqProject` and
`coqc` each listed `.v` file under Rocq Prover `9.1.1`. A CI job runs the
same build in the `rocq/rocq:9.1` container on every push.

Current Qed-closed state (see the companion Op paper §8.5 for the
authoritative inventory and Axiom/Parameter disclosure):

- `CompilationSoundness.v`: all nine Lex→Op compilation cases close with
  `Qed.` — `verdict_preservation_const`, `_sanctions`, `_var`,
  `_const_record`, `_const_list`, `_const_variant`, `_match`,
  `_defeasible`, `_fill`. Zero `Admitted.`
- `LexOpAdequacy.v`: top-level `lex_op_adequacy` plus supporting
  theorems `lex_op_adequacy_bisim`, `lex_op_adequacy_congruence`,
  `lex_op_adequacy_injective`, `admissible_compile_respects_verdict`
  close with `Qed.`
- `SessionCorridor.v`, `MPSTProjection.v`: six-message bilateral
  corridor deadlock-freedom, session safety, ack harmonisation, and
  duality theorems close with `Qed.` The message `payload` type is an
  uninterpreted `Parameter` in both files.
- `BSCInvariants.v`: invariants I1/I2/I3 and the per-rule preservation
  theorems close with `Qed.` over an abstract four-component corridor
  history record.
- `WireFormatVerifier.v`: the five-byte canonical wire format's
  round-trip, injectivity, determinism, and six rejection-class
  theorems close with `Qed.`
- `LexVerdictEmbedding.v`: the Lex→Op verdict embedding `lex_to_op`
  and its properties (injective, rank-monotone, meet-preserving)
  close with `Qed.`
- `CanonicalEncoding.v`, `ComplianceContext.v`, `EffectRow.v`: each
  closes its module-local Qed obligations.

Five paper-level theorems — termination, progress, subject reduction,
effect monotonicity, and parallel confluence — are Qed-closed only over
concrete toy fragments (lambda calculus in `OpProgressSubject.v`, a
nine-constructor gasified AST in `OpConcreteAST.v`, a two-slot counter
machine in `OpEffectMonotonicity.v`). The abstract Module Type in
`OpPaperTargetsModuleType.v` is witnessed by these toy instances in
`OpPaperTargetsInstance.v`. Inhabitation of the Module Type by a toy
instance does not establish the theorem for Op proper.

Axioms and Parameters beyond `CompilationSoundness.host_sanctions` and
`CompilationSoundness.prelude` exist in several parametric-interface
modules (`BundleAppendOnly.v`, `CorridorMonotone.v`, `GasTermination.v`,
`UpToTauCompatibility.v`, `HeteroBisimulation.v`, plus
`MPSTProjection.payload` / `SessionDuality.payload`). Op paper §8.5
itemises every file- or module-level `Parameter` and `Axiom` in the
mechanization. No classical axioms are imported or used.

### Formal artifacts (Lean)

```
formal/lean/OpCore.lean
```

The Lean mirror is provided as a scaffold. A Lean toolchain is not wired into
CI.

## Benchmarks

The workspace exposes Criterion benchmarks and a proof-bundle size example:

```
cargo bench -p op-core --bench op_pipeline
cargo bench -p op-lex-compiler --bench compile_lex
cargo run --release -p op-core --example bundle-size
```

`docs/benchmarks.md` records one empirical snapshot and the exact harness
commands. Treat benchmark numbers as measurements to be regenerated on the
reviewer's hardware, not as proof obligations.

## Hardware and timing

The numbers below are indicative. CI runs on `ubuntu-latest` GitHub-hosted
runners.

| Step | Cold (macOS M-series, 10-core) | Warm (macOS M-series, 10-core) |
|---|---|---|
| `cargo check --workspace` | ~35 s | ~3 s |
| `cargo test --workspace` (build + run) | ~60 s | ~5 s |
| `coqc CompilationSoundness.v` | ~3 s | ~3 s |
| `cargo run --example hello-op -p op-core` (first run) | ~6 s | <1 s |

Disk footprint for the compiled `target/` directory is ~400 MB.

## Determinism

- Proof-bundle digests are reproduced across runs; see
  `crates/op-core/tests/proof_bundle_determinism.rs`.
- Compiled Op programs for a fixed source are byte-identical across runs;
  see `crates/op-lex-compiler/tests/golden_*.rs`.
- Meet-monotonicity across cross-zone composition is exercised by proptest;
  see `crates/op-core/tests/meet_monotonicity.rs`.

## Environment

The workspace compiles and tests cleanly on:

- Ubuntu 22.04 / 24.04 (x86_64)
- macOS 13+ (Apple Silicon)

No network access is required after the initial `cargo fetch`. The workspace
has no network-dependent tests.

## Issues

If `cargo test --workspace` reports a count other than `97` passed, or if any
example deviates from the output above, please open an issue at the repository
with the full `rustc --version`, `cargo --version`, and platform information.
