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

- Channel: `1.84.0` (stable)
- Components: `rustfmt`, `clippy`
- Profile: `minimal`

`rustup` honors this file automatically. The workspace MSRV declared in
`Cargo.toml` is `1.76`; the pin sits above MSRV and is the version CI runs.

Coq mechanization is checked against:

- Rocq Prover `9.1.1` (or compatible `9.x` — the container image
  `rocq/rocq:9.1` is used by CI).

## Expected results

### Rust workspace

```
cargo test --workspace
```

Expected: `86` tests pass across the four crates `op-core`, `op-compiler`,
`op-stdlib`, `op-lex-compiler`. Zero failures. Doc-tests contribute one
`ignored` entry from `op_lex_compiler` (signature-only).

Breakdown by crate at the time this document was written:

| Crate | Unit tests | Integration tests | Total |
|---|---|---|---|
| `op-compiler` | 8 | 0 | 8 |
| `op-core` | 27 | 21 | 48 |
| `op-lex-compiler` | 11 | 12 | 23 |
| `op-stdlib` | 7 | 0 | 7 |

Integration test binaries: `compensation_runtime`, `meet_monotonicity`,
`proof_bundle_determinism` (op-core); `golden_defeasible_tolling`,
`golden_flat_fsmr`, `golden_sanctions` (op-lex-compiler).

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
coqc OpCore.v
coqc CompilationSoundness.v
```

Both commands exit `0` with no diagnostic output on Rocq `9.1.1`. A CI job
runs these commands in the `rocq/rocq:9.1` container on every push.

`CompilationSoundness.v` closes the scalar-constant case and the
sanctions-dominance case with `Qed.` (full proofs). The remaining seven
obligations listed in `formal/coq/README.md` are registered as `Admitted`
theorems with declared proof strategies.

### Formal artifacts (Lean)

```
formal/lean/OpCore.lean
```

The Lean mirror is provided as a scaffold. A Lean toolchain is not wired into
CI.

## Benchmarks

The workspace does not yet expose Criterion benchmarks. Performance claims in
the paper are not executable from this repository.

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

If `cargo test --workspace` reports a count other than `86` passed, or if any
example deviates from the output above, please open an issue at the repository
with the full `rustc --version`, `cargo --version`, and platform information.
