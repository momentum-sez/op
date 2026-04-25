# Op

[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)
[![CI](https://github.com/momentum-sez/op/actions/workflows/ci.yml/badge.svg)](https://github.com/momentum-sez/op/actions/workflows/ci.yml)
[![Coq](https://github.com/momentum-sez/op/actions/workflows/coq.yml/badge.svg)](https://github.com/momentum-sez/op/actions/workflows/coq.yml)
[![Release](https://img.shields.io/badge/release-0.1.0-orange.svg)](https://github.com/momentum-sez/op/releases)
[![Rust](https://img.shields.io/badge/rust-1.86.0-brown.svg)](rust-toolchain.toml)

Op is a typed, stack-based bytecode and deterministic operational semantics for
compliance-carrying operations in sovereign institutional kernels. An Op
program is a directed acyclic graph of typed steps with an explicit effect
row, precondition and postcondition contracts, a scoped compensation branch
attached to the step it inverts, and explicit suspension and resumption
semantics for callback events. Reduction is deterministic and metered by a
two-axis gas model that separates structural cost from extensional cost, and
every execution produces a content-addressed proof bundle sufficient to replay
the operation on any host that shares the program definition, input bundle,
pack digest, oracle log, and deterministic primitive semantics.
Lex, the rule language for jurisdictional compliance, compiles into Op:
`docs/language-spec.md` is the language surface, and the paper *Op: A Typed
Bytecode for Compliance-Carrying Operations* at research.momentum.inc is the
formal treatment.

## What is new

Op is the first typed bytecode in which the primitives of institutional
workflow are **language grammar**, not library idiom. Five features
distinguish it.

1. **Effect rows with a sanctions-dominance law.** Tracked effects are
   path-indexed; any reachable state mutation not dominated by a sanctions
   check fails to type-check.

2. **Typed suspension.** `await e within d` is a typed construct whose
   continuation is serialized into the proof bundle, so suspension is as
   replayable as computation.

3. **Local compensation.** `compensate { … }` attaches syntactically to the
   step it inverts; the rollback plan is derived by the compiler from the
   forward DAG.

4. **Linear and locked resources.** `Linear<T>` and the specified indexed
   typestates `Locked<T, omega, epsilon>`, `Signed<T, omega, epsilon>`,
   `Verified<omega, epsilon>`, and `Blame<omega, epsilon, reason>` lift
   bilateral cross-zone commit obligations into the type surface. The current
   Rust AST exposes the narrower unindexed `Locked<T>` prototype while the
   indexed surface is closed formally.

5. **Bilateral cross-zone composition.** Composition across two zones
   produces verdicts via the pointwise meet on the compliance lattice. The
   n-party MPST generalisation is a declared target, not a closed theorem in
   this repository.

**Prior art.** EVM (Wood, 2014) and WebAssembly (Haas et al., 2017) share
the typed-bytecode and determinism commitments but treat compliance effects,
suspension, and compensation as host concerns. Michelson (Allombert et al.,
2018) shares the typed stack and formal semantics but is transaction-atomic
and has no non-atomic suspension or cross-zone commit. Move (Blackshear et
al., 2019) provides the linear-resource discipline Op specializes for
compliance-carrying workflows and extends with locked typestates for
cross-zone commit resources. Op's contribution is the combination — typed
effects with a sanctions-dominance law, typed suspension, local compensation,
linear and locked resources, and pairwise-replayable cross-zone execution —
all as primitive grammar.

## Why it matters

A compliance workflow written in Op is a workflow whose execution trace is
its audit and whose replay is its verification. The proof bundle is
append-only and content-addressed; a second zone re-runs the program against
the same inputs, pack digest, and oracle log and compares bundles
digest-by-digest.

The design target is five conservation invariants — gas conservation, resource
linearity, ownership conservation, audit monotonicity, and meet-monotonicity of
compliance state across zone composition. The repository contains scoped
machine-checked evidence for these claims over the fragments named below; full
Op-proper progress, preservation, effect monotonicity, parallel confluence, and
concrete payload integration remain open.

Classes of error that institutional workflows habitually tolerate — a
skipped sanctions check, an unreversed registry filing, an uncoordinated
cross-zone commit, an ambiguous writer on a state change — are not
reachable because they are not expressible in the grammar.

## Run it

```bash
cargo run --example hello-op -p op-core
```

Output:

```
program      : hello.op  (jurisdiction: _default)
typecheck    : OK  (composed effects: [SovereignWrite, SanctionsCheck])
gas bound    : 20 structural units
step gate      : screening.sanctions -> COMPLETED
step activate  : update.entity_status -> COMPLETED
verdict      : ADMIT  (2 steps executed, trace is replayable)
```

The example constructs a two-step program (a `sanctions_check`-dominated gate
followed by a `sovereign_write` activation), type-checks it against the
effect-row discipline, and dispatches both primitives through the built-in
`NoopHost`. The source is `crates/op-core/examples/hello-op.rs`.

## Reading path

The repository is organised in three layers; the boundary between them is
load-bearing for every claim in the paper.

**Executable — what the type checker accepts and what `cargo run` invokes.**

- `docs/language-spec.md` — canonical language reference: grammar, type
  system, effect system, contracts, compensation, multi-entity operations,
  jurisdiction resolution, gas, policy blocks, EBNF.
- `crates/op-core/` — language core: AST, type checker, effect-safety
  analyser, gas model, evaluator, host trait.
- `crates/op-compiler/`, `crates/op-stdlib/`, `crates/op-lex-compiler/` —
  YAML lowering, canonical primitive corpus, Lex→Op compilation function.
- `examples/incorporate.op`, `examples/letter-of-credit.op` — worked
  programs over the canonical primitive corpus.

**Mechanized evidence — scoped Qed results and disclosed boundaries.**

- `formal/coq/` — Coq mechanisation: `OpCore.v` and `OpMetaTheory.v` for
  the language; `BSCInvariants.v`, `BundleAppendOnly.v`,
  `EffectRow.v`, `GasTermination.v`, `OpEffectMonotonicity.v`,
  `OpProgressSubject.v` for conservation invariants;
  `CompilationSoundness.v`, `LexOpAdequacy.v`, `LexVerdictEmbedding.v`,
  `UpToTauCompatibility.v` for the Lex→Op verdict-preservation theorem over
  the scalar admissible skeleton; `SessionCorridor.v`, `SessionDuality.v`,
  `MPSTProjection.v`, `HeteroBisimulation.v` for the binary, payload-parametric
  corridor skeleton; `WireFormatVerifier.v`, `CanonicalEncoding.v` for a small
  canonical wire-format fragment. Several files intentionally use `Parameter`
  or `Axiom`; `formal/coq/README.md` and the Op paper itemise them.
- `formal/lean/OpCore.lean` — Lean mirror.

**Frontier — milestones declared but not yet closed.**

- `formal/coq/Op/` — F-OP-FORMAL milestone scaffolds (`Syntax.v`,
  `Semantics.v`); typing relation, progress, preservation, and the
  Lex→Op compiler-correctness theorem are queued for later milestones.

**Paper.** *Op: A Typed Bytecode for Compliance-Carrying Operations* at
research.momentum.inc — formal small-step operational semantics, scoped
conservation evidence, Lex→Op verdict preservation for the admissible scalar
skeleton, binary cross-zone replay and commit typing, prior-art placement, and
open problems.

## Repository layout

```text
op/
|-- crates/
|   |-- op-core/           language, type checker, effect system, gas model, host trait
|   |-- op-compiler/       YAML and source to Op bytecode lowering
|   |-- op-stdlib/         canonical primitive corpus
|   |-- op-lex-compiler/   Lex -> Op compilation function (paper §6.2)
|-- docs/
|   |-- language-spec.md
|-- examples/
|   |-- incorporate.op
|   |-- letter-of-credit.op
|-- formal/
|   |-- coq/               language, conservation invariants, Lex->Op soundness
|   |-- lean/              OpCore.lean mirror
|-- Cargo.toml
|-- LICENSE
|-- README.md
```

The workspace compiles standalone from a cold clone; it has no path
dependencies on external checkouts.

```bash
cargo check --workspace
cargo test  --workspace
cargo clippy --workspace -- -D warnings
```

## Relation to Lex

Lex is the rule and proof layer. Op is the workflow layer. Their interface is
preconditions, postconditions, and effect discharge: a Lex predicate compiles
into an Op boolean expression, a Lex defeasible rule compiles into a guarded
`choose`, and a Lex compliance-fiber verdict compiles into an Op
`ensures domains` declaration. Op does not re-interpret Lex semantics at
runtime; compilation is content-addressed and version-pinned at authoring
time. Lex lives at <https://github.com/momentum-sez/lex>.

## Reproducibility

See [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md) for the exact toolchain pin,
expected test counts, example outputs, and hardware budgets. The repository
ships with a pinned Rust toolchain (`rust-toolchain.toml`), GitHub Actions
CI for Rust and Rocq, and a self-contained workspace that compiles from a
cold clone without sibling checkouts.

## Contributing

Issues and pull requests welcome. Before opening a pull request, run:

```bash
cargo test  --workspace
cargo clippy --workspace -- -D warnings
```

New primitives are added to `crates/op-stdlib` with a typed signature, a
default effect row, and a lowering rule to a canonical host call; extensions
to the language surface should cite the corresponding section of
`docs/language-spec.md` or the paper and include tests in `crates/op-core`.

## License

Apache-2.0. See [`LICENSE`](LICENSE).
