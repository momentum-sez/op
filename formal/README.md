# Op Core — Formal Scaffolds

Companion mechanizations of the Op language core. The scaffolds formalize the
core typing judgment, effect-row algebra, and linearity / lock discipline.

## Layout

- `coq/OpCore.v` — Coq scaffold.
- `lean/OpCore.lean` — Lean scaffold.

## Status

Placeholder. Neither scaffold has been populated with mechanized proofs yet.
The target obligations are:

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
