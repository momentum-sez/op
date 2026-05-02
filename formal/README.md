# Op Core — Formal Scaffolds

Companion mechanizations of the Op language core. The scaffolds formalize the
core typing judgment, effect-row algebra, and linearity / lock discipline.

## Layout

- `coq/OpCore.v` — Coq scaffold.
- `lean/OpCore.lean` — Lean scaffold.

## Status

The Coq tree contains scoped closed fragments: effect-row algebra,
bundle-append monotonicity, gas termination, Op progress/subject reduction
for the modeled fragment, Lex verdict embedding, and the nine-case
`L_adm -> Op` verdict-preservation skeleton. The Lean tree remains a
scaffold. The `coq/Op/` subtree is an M-F1 syntax/semantics scaffold for Op
proper; full Op-proper compiler correctness, preservation, and progress are
still target obligations.

The remaining obligations are:

- **Type preservation under lowering.** For every well-typed Op program `e`,
  its lowered YAML operation-definition `[[e]]` preserves the typing judgment.
- **Effect safety.** Any reachable write-class effect (`sovereign_write`,
  `identity_mutation`, `fiscal_transfer`) is dominated by a `sanctions_check`,
  modulo the deferred-subject exception for entity creation.
- **Linearity soundness.** A linear resource is consumed at most once.
- **Lock duality.** A `Locked<T>` resource has exactly two eliminators
  (`commit_transfer`, `release_lock`); a well-typed program uses exactly one.
- **Gas bound correctness.** The static structural-gas bound upper-bounds
  the number of structural reductions any execution performs.

## Relation to the Rust reference

The Rust reference implementation in `crates/op-core/` is the executable
witness for the forward direction of the decidability lemma for the
admissible program fragment. Each formal construct planned above has a Rust
counterpart:

| Formal construct            | Rust module                |
|-----------------------------|----------------------------|
| `OpType` / `Effect`         | `ast`                      |
| Typing judgment             | `types`                    |
| Effect-row algebra          | `effects`                  |
| Structural gas model        | `gas`                      |
| Deterministic reduction     | `evaluator` (planned)      |
