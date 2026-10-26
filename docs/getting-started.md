# Getting Started with Op

Build the workspace, run its tests, and inspect an Op program through the
public host interface. Install Rust and Cargo before starting.

## 1. Clone and build

```bash
git clone https://github.com/momentum-sez/op.git
cd op
cargo check --workspace
```

The workspace has no external path dependencies. The pinned toolchain and
initial dependency downloads can affect build time.

## 2. Run the tests

```bash
cargo test --workspace
```

The workspace contains four crates: `op-core`, `op-compiler`, `op-stdlib`,
and `op-lex-compiler`. All selected tests must pass. Use the command output
for current totals and ignored tests. Tests cover type checking, effect safety,
resource use, lowering, the primitive corpus, and Lex compilation.

## 3. Run the instant-demo example

```bash
cargo run --example hello-op -p op-core
```

The example constructs an `OpProgram` and checks its declared effects.
The `gate` step supplies the sanctions check before the `activate` step's
state-write effect. The checker also computes a static structural gas bound.

The example then calls each primitive through `NoopHost`, which returns a
deterministic JSON record. Its final line reports an illustrative walk.
The walk does not meter gas, apply a real state mutation, or produce a signed
proof or admission verdict.

Read `crates/op-core/examples/hello-op.rs` alongside its output.
Run `cargo test -p op-core --example hello-op` to check the example's acceptance
conditions.

## 4. Run the compliance-gate example

```bash
cargo run --example compliance-gate -p op-core
```

The program encodes a policy: deny if the counterparty's jurisdiction is
on a sanctions list AND the amount exceeds a threshold. The example runs
the program against two scenarios — one that admits, one that denies —
and prints the proof-certificate shape (program digest, composed
effects, gas, trace, verdict) for each.

Source: `crates/op-core/examples/compliance-gate.rs`.

Run the example's unit tests alongside:

```bash
cargo test --example compliance-gate -p op-core
```

## 5. Read the spec

```bash
open docs/language-spec.md   # macOS
xdg-open docs/language-spec.md   # Linux
```

Section 1 is the 500-word accessible summary: what Op is, the
instruction set, a two-line example. Sections 2–13 are the full
reference: type system, effect system, contracts, compensation,
multi-entity operations, jurisdiction resolution, gas, policy blocks,
the host ABI, the EBNF grammar, and worked examples.

Two surface-syntax example programs live at:

- `examples/incorporate.op` — minimum entity incorporation.
- `examples/letter-of-credit.op` — bilateral cross-zone trade finance.

Read both after the spec. They show how the grammar feels in practice.

## 6. Write your first Op program

The simplest workflow: a sanctions-gated state mutation. Create
`my-first.op` at the repo root:

```op
op my.activate for _default
version "0.1.0"

inputs {
  entity_id: EntityId
}

effects {
  sanctions_check;
  sovereign_write;
}

do {
  run gate = screening.sanctions({ subject_id: entity_id });
  run activate = update.entity_status({
    entity_id: entity_id,
    status: "ACTIVE"
  });
  return { status: activate.status };
}
```

The `.op` surface syntax is not executable directly; it is the authoring
surface that lowers into the same AST the Rust embedding builds.
Alternatively, author directly in Rust against `op-core`:

```rust
use op_core::{typecheck_program, Effect, OpProgram, OpStep, OpType, ...};

let program = OpProgram { /* ... */ };
let check = typecheck_program(&program);
assert!(check.success);
```

`crates/op-core/examples/hello-op.rs` is a complete template.

## 7. Connect a real host

`NoopHost` is the test / example host. A real embedding implements the
`OpHost` trait:

```rust
use op_core::host::{HostError, HostOutcome, OpHost, PrimitiveCall};

pub struct MyHost { /* kernel handle, db pool, ... */ }

impl OpHost for MyHost {
    fn invoke(&self, call: &PrimitiveCall) -> Result<HostOutcome, HostError> {
        match call.primitive.0.as_str() {
            "screening.sanctions" => { /* hit your screening backend */ }
            "update.entity_status" => { /* commit the mutation */ }
            other => Err(HostError::UnknownPrimitive(other.to_string())),
        }
    }
}
```

`crates/op-core/examples/compliance-gate.rs` shows a complete host with
rule logic — read it as a template.

## 8. What to read next

The repository is organised in three layers; reading paths into each are
distinct.

**Executable — what the type checker accepts and what `cargo run` invokes:**

- `docs/language-spec.md` — the full language reference.
- `crates/op-core/src/types.rs` — the type checker.
- `crates/op-core/src/effects.rs` — the effect-safety analyser.
- `crates/op-core/src/gas.rs` — the two-tier gas model.
- `crates/op-compiler/src/lower.rs` — YAML → Op lowering.
- `crates/op-stdlib/src/canonical.rs` — the canonical primitive corpus.
- `crates/op-lex-compiler/` — the Lex→Op compilation function.

**Mechanized evidence — scoped Qed results and disclosed boundaries:**

- `formal/coq/OpCore.v`, `formal/coq/OpMetaTheory.v` — base-sort scaffold
  and admissible-fragment metatheory.
- `formal/coq/{BSCInvariants,BundleAppendOnly,EffectRow,GasTermination,
  OpEffectMonotonicity,OpProgressSubject}.v` — the five conservation
  invariants.
- `formal/coq/{CompilationSoundness,LexOpAdequacy,LexVerdictEmbedding,
  UpToTauCompatibility}.v` — Lex→Op verdict preservation.
- `formal/coq/{SessionCorridor,SessionDuality,MPSTProjection,
  HeteroBisimulation}.v` — cross-zone replay and three-phase commit.
- `formal/lean/OpCore.lean` — Lean mirror of the language scaffold.

These files are evidence with named scope, not a blanket proof of Op proper.
The closed Lex-to-Op result is verdict preservation for the admissible scalar
skeleton. Several files intentionally declare `Parameter` or `Axiom` interfaces
for host sanctions, prelude lookup, payloads, bundle append behavior, gas
semantics, and hetero-bisimulation; `formal/coq/README.md` and the Op paper
itemise the inventory.

**Frontier — milestones declared but not yet closed:**

- `formal/coq/Op/` — F-OP-FORMAL Tier-5 scaffolds; typing, progress,
  preservation, and the compiler-correctness theorem are queued for later
  milestones.

The paper *Op: A Typed Bytecode for Compliance-Carrying Operations* at
research.momentum.inc describes the formal semantics, the conservation
invariants, and the soundness property. Read it when you want the mathematics
beneath the code.
