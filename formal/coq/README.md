# Op Core — Coq mechanization

Coq sources backing the formal obligations enumerated in `formal/README.md`.

## Files

- `OpCore.v` — base scaffold: enumeration of Op sort names; a reflexivity
  lemma as a typecheck smoke test.
- `CompilationSoundness.v` — verdict preservation for the compilation
  function `[[.]] : Lex -> Op` from the Op paper §6.2, mechanized for
  the scalar shape of the constant compilation case and for the
  sanctions-dominance case.

## What `CompilationSoundness.v` mechanizes

### Scalar constant case

For the admissible Lex fragment restricted to the constant head
constructor over first-order scalar values (unit, boolean, integer,
string):

1. A minimal Lex AST with first-order scalar base values.
2. A minimal Op expression AST covering the literal forms the scalar
   constant compilation case produces.
3. The value-lifting function `lift_value : LexValue -> OpExpr`,
   matching the scalar cases of the Rust reference in
   `crates/op-lex-compiler/src/lift.rs`.
4. The compilation function `compile : LexTerm -> OpExpr` for the
   constant case, matching the Rust reference in
   `crates/op-lex-compiler/src/case_const.rs`.
5. Small-step operational semantics for Lex and Op with a label
   alphabet distinguishing silent `tau` transitions from observable
   verdict emissions.
6. Verdict-extraction predicates `lex_verdict` and `op_verdict`.
7. Two operational lemmas — `lift_value_emits` (the lifted expression
   emits the source value) and `lift_value_emits_unique` (the
   emitted value is uniquely determined by the source value).
8. The main biconditional `verdict_preservation_const` — for every
   scalar Lex constant, the Lex-level verdict and the Op-level
   verdict coincide.
9. Uniqueness theorems for the constant verdict in both languages.
10. Four end-to-end examples (boolean, integer, string, unit).

The scalar case closes by case analysis on the base value. Both
directions of the biconditional are discharged with `Qed.`

### Sanctions-dominance case

For the §6.2 / §6.3 sanctions-dominance rule, restricted to a
scalar-constant principal:

1. A concrete Lex head `SLT_Sanctions` layered over the scalar
   constant fragment, plus a concrete Op host-call form
   `SOE_Call "sanctions.check" · ` taking a single named argument.
2. The host primitive `host_sanctions : LexValue -> LexValue`
   axiomatized with a two-element range
   (`"Compliant"` or `"SanctionsBlocked"`).
3. Small-step reductions on both sides threading the principal's
   scalar through the host call before emitting the verdict.
4. The compilation function `sanct_compile` matching the Rust
   reference in `crates/op-lex-compiler/src/case_sanctions.rs`.
5. Injectivity of `lift_value` and the helper
   `sanct_op_lit_emit_unique` discharging the uniqueness of the
   scalar emission under the `SOE_Lit` wrapper.
6. The main biconditional `verdict_preservation_sanctions` closing
   both directions with `Qed.`.
7. A two-valued sanity example `sanctions_verdict_is_two_valued`.

The file type-checks under `coqc` (Rocq Prover 9.1.1) with no errors
and no warnings.

## Proof obligations

The §6.2 compilation function comprises six cases. The scalar shape
of the constant case and the sanctions-dominance case are closed
(`Qed.`). Seven obligations remain, registered in the `Obligations`
section at the foot of `CompilationSoundness.v`, with a
proof-structure comment for each:

| Obligation | Shape | Strategy |
|---|---|---|
| Constant — record | `LV_Record fields` | Structural induction with nested induction on the field list. |
| Constant — list | `LV_List elems` | Structural induction with nested induction on the element list. |
| Constant — variant | `LV_Variant tag payload` | Structural induction, reducing to the record-shape obligation via the two-field record encoding. |
| Variable | `Var name` | Direct rewrite through the prelude-lookup equation. |
| Match | `Match scrutinee branches` | Induction on the branch list; base via the constant lemma. |
| Defeasible | `Defeasible name base exceptions` | Well-founded induction on `(priority DESC, source_position ASC)`. |
| HoleFill (§6.3) | `HoleFill hole_id filler witness` | Coinduction on a bisimulation relation pairing each Lex state with the Op state reached by unwinding one `tau` attestation-append step. |

Each obligation is written as an `Admitted.` theorem whose signature
matches the target result. The surrounding parameters
(`ExtLexTerm`, `ExtOpExpr`, `ExtCompile`, `ExtLexVerdict`,
`ExtOpVerdict`, and the syntactic constructors `ELV_*` / `ELT_*`)
stand in for the extended inductive definitions that a follow-on
file introduces by mirroring the Rust AST in
`crates/op-lex-compiler/src/ast.rs`.

## Running the typechecker

```
cd formal/coq
coqc CompilationSoundness.v
```

Exit code zero and no diagnostic output indicates the scalar case
is machine-verified by Rocq 9.1.1.

## Relation to the Rust reference

`CompilationSoundness.v` mirrors the Rust definitions in
`crates/op-lex-compiler/src/lift.rs` (`lift_value`),
`crates/op-lex-compiler/src/case_const.rs` (`compile_const`), and
`crates/op-lex-compiler/src/case_sanctions.rs` (`compile_sanctions`).
Each Coq definition is the mathematical companion of the
corresponding Rust function; every scalar base constructor handled
by the Rust `lift_value` is handled by the Coq `lift_value`, and
the sanctions-dominance compilation shape agrees. Extending the
Coq mechanization to the remaining shapes and cases is a matter of
mirroring the other `case_*.rs` files into the corresponding
inductive relations and discharging the obligations registered in
the `Obligations` section.
