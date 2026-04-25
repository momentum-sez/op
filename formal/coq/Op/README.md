# Op/ — F-OP-FORMAL milestone scaffolding

This subdirectory hosts the dedicated Op-language mechanisation
that targets the conservation invariants of `docs/language-spec.md`.

## Files

- `Syntax.v` — M-F1 deliverable: the abstract syntax of Op as a
  Rocq inductive type mirroring `crates/op-core/src/ast.rs::OpExpr`. Includes
  the value predicate `is_value`. No theorems about well-typedness
  or reduction — those live in later milestones.
- `Semantics.v` — M-F1 companion: small-step relation `step : OpExpr
  → OpExpr → Prop` for the call-by-value core. Covers Apply /
  Lambda / Let / If / Sequence / FieldAccess / AssertSafety /
  TryCatchCompensate. Sanity-check lemmas closed with trivial
  tactics.

## Coverage vs the Rust reference

The M-F1 scaffold covers the initial `OpExpr` variants modeled from
`crates/op-core/src/ast.rs`. Non-covered variants (`Await`, `AssertSafety`
subtypes, the full locked-handle discipline, intercalated safety
predicates) are deferred to later milestones.

Variants mechanized in `Syntax.v`:

| Coq constructor          | Rust counterpart                          |
|--------------------------|-------------------------------------------|
| `OE_Literal`             | `OpExpr::Literal`                         |
| `OE_Var`                 | `OpExpr::Var`                             |
| `OE_Apply`               | `OpExpr::Apply`                           |
| `OE_Let`                 | `OpExpr::Let`                             |
| `OE_Lambda`              | `OpExpr::Lambda`                          |
| `OE_Sequence`            | `OpExpr::Seq`                             |
| `OE_If`                  | `OpExpr::If`                              |
| `OE_Match`               | `OpExpr::Match` (shape only; reduction
                             deferred)                                  |
| `OE_RecordLit`           | `OpExpr::RecordLit`                       |
| `OE_FieldAccess`         | `OpExpr::FieldAccess`                     |
| `OE_ConsumeLinear`       | `OpExpr::ConsumeLinear`                   |
| `OE_Lock3PC`             | `OpExpr::Lock3PC`                         |
| `OE_CommitTransfer`      | `OpExpr::CommitTransfer`                  |
| `OE_ReleaseLock`         | `OpExpr::ReleaseLock`                     |
| `OE_TryCatchCompensate`  | `OpExpr::TryCatchCompensate`              |
| `OE_AssertSafety`        | `OpExpr::AssertSafety`                    |

## Ratchet discipline

- Zero `Admitted`.
- Zero `sorry`-equivalents.
- Ratchet down-only; raising requires reviewer sign-off.

This scaffold is purely declarative; no axioms introduced.

## Build

```
cd formal/coq
coqc -Q Op Op Op/Syntax.v
coqc -Q Op Op Op/Semantics.v
```

Exit 0 + no diagnostic output confirms Rocq 9.1.1 accepts the
encoding.

## Next milestones

| Milestone | File                                      |
|-----------|-------------------------------------------|
| M-F2      | `Op/Typing.v` — typing relation           |
| M-F3      | `Op/Progress.v` — progress theorem        |
| M-F4      | `Op/Preservation.v` — preservation theorem |
| M-F6      | `OpCompiler/Correctness.v` — Lex→Op correctness |

M-F5 (capability structural invariants) is out-of-tree: capability
discipline is an embedder-side property over `OpHost` and is mechanised
in the embedder's own formal tree.
