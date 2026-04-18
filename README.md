# Op

Op is a typed, stack-based bytecode and deterministic operational semantics for
compliance-carrying operations in sovereign institutional kernels. An Op
program is a directed acyclic graph of typed steps with an explicit effect
row, precondition and postcondition contracts, a scoped compensation branch
attached to the step it inverts, and explicit suspension and resumption
semantics for callback events. Reduction is deterministic and metered by a
two-axis gas model that separates structural cost from extensional cost, and
every execution produces a content-addressed proof bundle sufficient to replay
the operation on any kernel that shares the program definition and the inputs.
Lex, the rule language for jurisdictional compliance, compiles into Op:
`docs/language-spec.md` is the language surface, and `~/momentum-research/papers/op.md`
is the formal treatment.

## What is new

Op is the first typed bytecode in which the primitives of institutional
workflow are language grammar rather than library idiom: a tracked effect row
with a sanctions-dominance law that rejects any reachable state mutation not
dominated by a sanctions check; `await e within d` as a typed construct whose
continuation is serialized into the proof bundle, so suspension is as
replayable as computation; compensation attached syntactically to the step it
inverts, with the rollback plan derived by the compiler from the forward DAG;
`Linear<T>` and `Locked<T>` typestates that lift the three-phase commit of a
cross-zone operation into a static invariant, consumed only by
`commit_transfer` or `release_lock`; and multi-participant composition whose
verdict is the pointwise meet on the compliance lattice, monotonic by
construction. The closest neighbors are EVM (Wood, 2014) and WebAssembly
(Haas et al., 2017), which share the typed-bytecode and determinism commitments
but treat compliance effects, suspension, and compensation as host concerns;
Michelson (Allombert et al., 2018), which shares the typed stack and formal
semantics but is transaction-atomic and has no non-atomic suspension or
cross-zone commit; and Move (Blackshear et al., 2019), whose linear-resource
discipline Op adopts wholesale and extends with the `Locked<T>` typestate for
multi-zone commit resources. Op's contribution is the combination: typed
effects with a sanctions-dominance law, typed suspension, local compensation,
linear and locked resources, and pairwise-replayable cross-zone execution, all
as primitive grammar.

## Why it matters

A compliance workflow written in Op is a workflow whose execution trace is its
audit and whose replay is its verification. The proof bundle is append-only
and content-addressed; a second zone re-runs the program against the same
inputs and the same pack digest and compares bundles digest-by-digest, with
agreement accepting the first zone's claim and disagreement pinpointing a
specific semantic divergence. Five conservation invariants hold by
construction — gas conservation, resource linearity, ownership conservation,
audit monotonicity, and meet-monotonicity of compliance state across zone
composition — and the compilation from the admissible fragment of Lex into Op
preserves verdict semantics up to weak bisimulation. Classes of error that
institutional workflows habitually tolerate — a skipped sanctions check, an
unreversed registry filing, an uncoordinated cross-zone commit, an ambiguous
writer on a state change — are not reachable because they are not expressible
in the grammar.

## Run it

```bash
cargo run --example hello-op -p op-core
```

Output:

```
program 'hello.op' type-checks cleanly
host completed: {"args":{"subject_id":"entity-xyz"},"jurisdiction":"_default","primitive":"screening.sanctions"}
```

The example constructs a two-step program (a `sanctions_check`-dominated gate
followed by a `sovereign_write` activation), type-checks it against the
effect-row discipline, and dispatches the first primitive through the built-in
`NoopHost`. The source is `crates/op-core/examples/hello-op.rs`.

## Reading path

- `docs/language-spec.md` — canonical language reference: grammar, type
  system, effect system, contracts, compensation, multi-entity operations,
  jurisdiction resolution, gas, policy blocks, EBNF.
- `~/momentum-research/papers/op.md` — formal treatment: small-step
  operational semantics, conservation invariants with proof sketches,
  compilation from Lex with a verdict-preservation theorem, cross-zone replay
  and the three-phase commit typed on `Locked<T>`, prior-art placement, and
  open problems.
- `formal/coq/OpCore.v` and `formal/lean/OpCore.lean` — mechanization
  scaffolds targeting the conservation invariants.
- `examples/incorporate.op` and `examples/letter-of-credit.op` — worked
  programs over the canonical primitive corpus.

## Repository layout

```text
op/
|-- crates/
|   |-- op-core/       language, type checker, effect system, gas model, host trait
|   |-- op-compiler/   YAML and source to Op bytecode lowering
|   |-- op-stdlib/     canonical primitive corpus and host trait
|-- docs/
|   |-- language-spec.md
|-- examples/
|   |-- incorporate.op
|   |-- letter-of-credit.op
|-- formal/
|   |-- coq/           OpCore.v
|   |-- lean/          OpCore.lean
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
