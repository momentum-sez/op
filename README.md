# Op

Op is a typed effectful workflow language for multi-step economic programs.
Step composition is explicit, steps have typed inputs and outputs, operational
effects are tracked statically, compensation attaches to the forward program it
inverts, and proof obligations are first-class constructs.

## Why Op

Workflow definitions encoded in untyped configuration files (YAML, JSON) carry
language semantics that exceed configuration:

- step composition through `depends_on` edges,
- variable binding and projection through string-path interpolation,
- control flow through embedded expression fragments,
- suspension and resumption through callback tokens,
- failure policy through ad hoc enumerations,
- inverse execution through detached compensation blocks.

These are language jobs. Op makes them language features. A program that
type-checks composes correctly, accounts for its effects, preserves its
compensation scope, and lowers deterministically to an execution plan.

## Design

- **Typed steps.** Every step carries an input type, an output type, and an
  effect row: `step s : In -> Out ! E`.
- **Compositional operators.** Sequential `a ; b`, parallel `par { ... }`,
  guarded choice `choose { ... }`, callback suspension `await e within d`, and
  scoped compensation `compensate { ... }`.
- **Effect tracking.** The effect row records the operational consequences of
  execution: sovereign write, identity mutation, fiscal transfer, sanctions
  check, governance request, document generation, external read, proof
  emission, and callback waits. A program that carries `sovereign_write` must
  be dominated by a `sanctions_check`, with one specific deferred exception
  for entity creation where the subject does not yet exist.
- **Typed binding.** Bindings are named and typed; `steps.y.result.z` becomes
  `y.z` against a structural record.
- **Typed await.** A waiting step returns `Await<Event, Payload>`. Waiting is
  operationally distinct from completion and the type system reflects that.
- **Local compensation.** Compensation attaches to the step it inverts. The
  compiler derives a reverse-topological rollback plan from the forward DAG.
- **Two-tier gas.** Structural gas is statically bounded by the program shape;
  extensional gas is metered against runtime cardinality certificates.
- **Host abstraction.** Op ships as a language and VM. Host primitives
  (compliance packs, proof systems, attestation backends) plug in through
  a host trait, allowing the same Op program to run against different
  sovereign execution contexts.

## Repository layout

```text
op/
├── crates/
│   ├── op-core/       language, type checker, evaluator, gas model
│   ├── op-compiler/   YAML / source -> Op bytecode lowering
│   └── op-stdlib/     canonical operation corpus and host trait
├── docs/
│   └── language-spec.md   canonical language reference
├── examples/
│   └── hello-op.rs    minimum-viable embedding
├── formal/
│   ├── coq/           formal scaffolds
│   └── lean/          formal scaffolds
├── Cargo.toml
├── CLAUDE.md
├── LICENSE
└── README.md
```

## Build and test

```bash
cargo check --workspace
cargo test --workspace
cargo clippy --workspace -- -D warnings
```

The workspace has no path dependencies on external checkouts. It compiles
standalone from a cold clone.

## Relation to Lex

Lex is the rule and proof layer. Op is the workflow layer. Their interface is
preconditions, postconditions, and effect discharge. A Lex program encodes a
typed jurisdictional rule; an Op step may reference Lex obligations through
`requires` and `ensures` contracts. Op does not redefine Lex semantics.

Lex lives at https://github.com/momentum-sez/lex.

## Contributing

Issues and pull requests welcome at the project repository. Run
`cargo test --workspace` before opening a pull request.

## License

Apache-2.0. See `LICENSE`.
