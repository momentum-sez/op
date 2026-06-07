# Op Core — Formal Scaffolds

Companion mechanizations of the Op language core. The scaffolds formalize the
core typing judgment, effect-row algebra, and linearity / lock discipline.

## Layout

- `coq/OpCore.v` — Coq scaffold.
- `lean/OpCore.lean` — Lean scaffold.

## Status

The Coq tree contains scoped closed fragments: effect-row algebra,
bundle-append monotonicity, gas termination (for an abstract gas-decreasing
step relation), progress/subject reduction *for a toy simply-typed-lambda
core* (`OpProgressSubject.v` — a small `E_Const/E_Var/E_Let/E_Lam/E_App`
calculus, NOT the real Op AST), Lex verdict embedding, and the nine-case
`L_adm -> Op` verdict-preservation skeleton. The Lean tree remains a
scaffold. The `coq/Op/` subtree is an M-F1 syntax/semantics scaffold for Op
proper (`Syntax.v`/`Semantics.v`; typing/progress/preservation are queued as
M-F2..M-F4). **Op-proper type soundness — progress, subject reduction, effect
monotonicity, parallel confluence, and Lex→Op compiler correctness over the
full Op AST — is NOT proved.** `OpPaperTargets.v` carries the paper-theorem
signatures plus concrete toy-fragment witnesses (no `Admitted` theorems), but
those witnesses establish only that the signatures are consistent, not the
paper theorems for Op proper.

The remaining obligations (all OPEN — none mechanized over Op proper) are:

- **Type preservation under lowering.** For every well-typed Op program `e`,
  its lowered YAML operation-definition `[[e]]` preserves the typing judgment.
- **Effect safety.** Any reachable write-class effect (`sovereign_write`,
  `identity_mutation`, `fiscal_transfer`) is dominated by a `sanctions_check`,
  modulo the deferred-subject exception for entity creation.
- **Linearity soundness** (UNMECHANIZED — design target). A linear resource is
  consumed at most once. There is no Coq/Lean proof of this property over the
  Op AST. It is enforced at runtime by the `op-core` type checker (hardened in
  the linear/affine type-system heal); the runtime check is the executable
  witness, not a formal proof.
- **Lock duality** (UNMECHANIZED — design target). A `Locked<T>` resource has
  exactly two eliminators (`commit_transfer`, `release_lock`); a well-typed
  program uses exactly one. There is no Coq/Lean proof of this property; the
  `op-core` runtime checker enforces the unindexed `Locked<T>` prototype. The
  indexed corridor surface is *modeled* (not proved closed) in the
  session-typed corridor files (`SessionCorridor.v`, `MPSTProjection.v`).
- **Gas bound correctness.** The static structural-gas bound upper-bounds
  the number of structural reductions any execution performs. `GasTermination.v`
  proves the abstract combinatorial core (any step relation with a strictly
  decreasing `nat` gas measure is strongly normalizing); the Op-proper instance
  is the open obligation.
- **Joint Lex⊕Op discharge soundness** (OPEN — file does not yet exist). The
  `lex_discharge_soundness` theorem described in
  `docs/proposal-lex-rule-contract-and-pack-binding.md` §"Coq/Lean" — that a
  type-checker-accepted Op program whose `structural_discharge` succeeds against
  a pack rule produces, on every execution, a Lex certificate that admissibly
  discharges that rule — is the soundness fence-post for the `Contract::LexRule`
  / pack-binding extension. Its target home is `formal/coq/Joint/Discharge.v`,
  which is NOT present in this tree. Until that file exists and the theorem is
  closed, `Contract::LexRule` is a data shape backed by the runtime checker, not
  a proved binding.

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
