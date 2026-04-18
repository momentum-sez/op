# Op Core — Coq mechanization

Coq sources backing the formal obligations enumerated in `formal/README.md`.

## Files

- `OpCore.v` — base scaffold: enumeration of Op sort names; a reflexivity
  lemma as a typecheck smoke test.
- `CompilationSoundness.v` — verdict preservation for the compilation
  function `[[.]] : Lex -> Op` from the Op paper §6.2, mechanized for
  the scalar shape of the constant compilation case, the
  sanctions-dominance case, the variable case, the record shape of
  the constant case, the list shape of the constant case, the
  variant shape of the constant case, and the match case
  (scalar-constant scrutinees, nullary-pattern branches,
  scalar-constant branch bodies).

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

### Variable case

For the §6.2 variable rule against a shared prelude:

1. Concrete Lex (`VarLexTerm`) and Op (`VarOpExpr`) AST extensions
   with constant and variable heads.
2. A shared deterministic prelude `prelude : string -> option
   LexValue` read from by both languages, enforcing identical
   lookup on each side.
3. Small-step reductions `var_lex_step` / `var_op_step` emitting
   the looked-up value when `prelude n = Some v`, with no emission
   rule for unbound names.
4. The compilation function `var_compile` mapping `VLT_Var n` to
   `VOE_Var n` and lifting constants.
5. The helper lemma `var_compile_shape_var` unfolding the compiled
   shape of a variable.
6. The main biconditional `verdict_preservation_var` closing both
   directions with `Qed.`.
7. The companion theorem `verdict_preservation_var_const`
   recovering the scalar-constant result inside the variable
   fragment, via the helper `var_op_lit_emit_unique`.

### Constant case — record shape

For the §6.2 constant case extended to records with scalar fields:

1. Concrete Lex (`RecLexTerm`) and Op (`RecOpExpr`) AST extensions
   carrying record-valued constants.
2. A pointwise field-emission relation `op_fields_emit` pairing the
   compiled Op field list with the source Lex field list.
3. Small-step reductions `rec_lex_step` / `rec_op_step` emitting
   the field list in one step; the emission payload is the field
   list itself, taking the bespoke `list (string * LexValue)` in
   place of the surrounding framework's scalar `LexValue` alphabet.
4. The compilation function `rec_compile` mapping a record-valued
   constant to the pointwise lifted Op record.
5. Two helper lemmas — `map_lift_value_emits` (the pointwise lifted
   field list emits the source list) and
   `map_lift_value_emits_unique` (the emitted list is uniquely
   determined by the source list), each proved by induction on the
   field list.
6. The main biconditional `verdict_preservation_const_record`
   closing both directions with `Qed.`.

### Constant case — list shape

For the §6.2 constant case extended to lists with scalar elements:

1. Concrete Lex (`ListLexTerm`) and Op (`ListOpExpr`) AST extensions
   carrying list-valued constants with scalar elements.
2. A pointwise element-emission relation `op_items_emit` pairing
   the compiled Op element list with the source Lex element list.
3. Small-step reductions `list_lex_step` / `list_op_step` emitting
   the element list in one step; the emission payload is the
   element list itself, taking the bespoke `list LexValue` in
   place of the surrounding framework's scalar `LexValue` alphabet.
4. The compilation function `list_compile` mapping a list-valued
   constant to the pointwise lifted Op list via `map lift_value`.
5. Two helper lemmas — `list_lift_value_emits` (the pointwise
   lifted element list emits the source list) and
   `list_lift_value_emits_unique` (the emitted list is uniquely
   determined by the source list), each proved by induction on the
   element list with injectivity of `lift_value` closing each
   element.
6. The main biconditional `verdict_preservation_const_list` closing
   both directions with `Qed.`.

### Constant case — variant shape

For the §6.2 constant case extended to variants with a tag (string)
and a scalar payload:

1. Concrete Lex (`VarLT`) and Op (`VarOE`) AST extensions carrying
   variant-valued constants with a tag and a scalar payload.
2. Small-step reductions `variant_lex_step` / `variant_op_step`
   emitting the `(tag, payload)` pair in one step; the emission
   payload is a `string * LexValue` pair, taking a bespoke
   relation.
3. The compilation function `variant_compile` mapping a variant
   constant to the tagged lifted payload.
4. The main biconditional `verdict_preservation_const_variant`
   closing both directions with `Qed.`, by direct inversion plus
   the scalar `lift_value_emits` / `lift_value_inj` lemmas on the
   payload.

### Match case

For the §6.2 match rule, restricted to scalar-constant scrutinees,
nullary-constructor patterns equated by scalar equality, and
scalar-constant branch bodies:

1. Concrete Lex (`MatchLexTerm`) and Op (`MatchOpExpr`) AST
   extensions carrying a scalar scrutinee and a list of
   (pattern, body) scalar pairs; the Op form is a choose-node
   over lifted scrutinee and lifted branches.
2. Decidable equality `LexValue_eq_dec` on `LexValue` delivered
   via `decide equality` with the standard scalar decidability
   lemmas.
3. A pair of pattern-matching selectors `lex_match_find` and
   `op_match_find` that walk the branch list in order, returning
   the first body whose pattern equals the scrutinee; on
   exhaustion both selectors return the fail-closed sentinel
   `lift_value fail_closed_value` (Op side) /
   `fail_closed_value = LV_Str "pattern_unmatched"` (Lex side),
   mirroring the Rust `fail_closed_expr` in `case_match.rs`.
4. Small-step reductions `match_lex_step` / `match_op_step`
   emitting the selector's result; the Op rule threads the
   scalar `op_step` emission through the selected branch body
   via a single explicit premise.
5. The compilation function `match_compile` mapping a scalar
   match term to the lifted choose-expression, via
   `map (fun (p, b) => (lift_value p, lift_value b))` over the
   branch list.
6. The key helper `op_match_find_lifts` — the lifted
   branch-selection selector agrees pointwise with the Lex-side
   selector. Proof by list induction; each step case-splits on
   pattern equality with injectivity of `lift_value` closing
   the residual on both branches.
7. The main biconditional `verdict_preservation_match` closing
   both directions with `Qed.`, by inversion on the match step
   plus the selector-agreement helper and the scalar
   `lift_value_emits` / `lift_value_emits_unique` lemmas.

The file type-checks under `coqc` (Rocq Prover 9.1.1) with no errors
and no warnings.

## Proof obligations

The §6.2 compilation function comprises seven closed cases: the
scalar shape of the constant case, the sanctions-dominance case,
the variable case, the record shape of the constant case, the list
shape of the constant case, the variant shape of the constant case,
and the match case. All seven close with `Qed.`. Two obligations
remain, registered in the `Obligations` section at the foot of
`CompilationSoundness.v`, with a proof-structure comment for each:

| Obligation | Shape | Strategy |
|---|---|---|
| Defeasible | `Defeasible name base exceptions` | Well-founded induction on `(priority DESC, source_position ASC)`. |
| HoleFill (§6.3) | `HoleFill hole_id filler witness` | Coinduction on a bisimulation relation pairing each Lex state with the Op state reached by unwinding one `tau` attestation-append step. |

Each obligation is an open theorem whose signature matches the
target result. The surrounding parameters (`ExtLexTerm`,
`ExtOpExpr`, `ExtCompile`, `ExtLexVerdict`, `ExtOpVerdict`, and the
syntactic constructors `ELT_*`) stand in for the extended inductive
definitions that a follow-on file introduces by mirroring the Rust
AST in `crates/op-lex-compiler/src/ast.rs`.

## Running the typechecker

```
cd formal/coq
coqc CompilationSoundness.v
```

Exit code zero and no diagnostic output indicates the seven
mechanized cases are machine-verified by Rocq 9.1.1.

## Relation to the Rust reference

`CompilationSoundness.v` mirrors the Rust definitions in
`crates/op-lex-compiler/src/lift.rs` (`lift_value`),
`crates/op-lex-compiler/src/case_const.rs` (`compile_const`,
record / list / variant shapes),
`crates/op-lex-compiler/src/case_sanctions.rs`
(`compile_sanctions`), `crates/op-lex-compiler/src/case_var.rs`
(`compile_var`), and `crates/op-lex-compiler/src/case_match.rs`
(`compile_match`, fail-closed sentinel `fail_closed_expr`). Each
Coq definition is the mathematical companion of the corresponding
Rust function; every scalar base constructor handled by the Rust
`lift_value` is handled by the Coq `lift_value`; the
sanctions-dominance, variable, record, list, variant, and match
compilation shapes agree. Extending the Coq mechanization to the
remaining cases is a matter of mirroring the other `case_*.rs`
files into the corresponding inductive relations and discharging
the obligations registered in the `Obligations` section.
