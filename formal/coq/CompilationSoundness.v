(** * CompilationSoundness.v

    Mechanization of verdict preservation for the compilation function
    [[.]] : Lex -> Op, restricted to the constant compilation case on
    first-order scalar values.

    Scope.

      - Lex AST (admissible fragment, constant head constructor,
        scalar payloads)
      - Op AST (expression fragment sufficient for lifted scalar
        constants)
      - value-lifting function [lift_value : LexValue -> OpExpr]
      - compilation function [compile : LexTerm -> OpExpr]
      - small-step operational semantics for Lex and Op with a trace
        alphabet distinguishing silent [tau] transitions from
        observable verdict emissions
      - verdict-extraction predicates on Lex terms and Op expressions
      - the verdict-preservation theorem for the scalar constant case,
        proved in both directions

    The proof closes with [Qed.]. The remaining shapes of the constant
    case (records, lists, variants) and the remaining five
    compilation cases (variable, match, defeasible,
    sanctions_dominance, hole_fill) are registered in the
    [Obligations] section as [Admitted.] theorems carrying honest
    proof-obligation statements that a follow-on mechanization will
    discharge. *)

Set Implicit Arguments.

From Stdlib Require Import List Bool ZArith String.
Import ListNotations.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(**  1.  Base datatypes shared between Lex and Op.                    *)
(* ------------------------------------------------------------------ *)

(** First-order scalar values recognized by the admissible Lex
    fragment. The Rust reference in [crates/op-lex-compiler/src/
    ast.rs] additionally carries records, lists, and variants;
    those shapes are registered in the obligations section below. *)

Inductive LexValue : Type :=
  | LV_Unit : LexValue
  | LV_Bool : bool   -> LexValue
  | LV_Int  : Z      -> LexValue
  | LV_Str  : string -> LexValue.

(** The Op expression fragment needed to receive a lifted Lex scalar.
    The full Rust [OpExpr] is substantially larger; the scalar
    constant case produces only the four literal forms below. *)

Inductive OpExpr : Type :=
  | OE_Unit : OpExpr
  | OE_Bool : bool   -> OpExpr
  | OE_Int  : Z      -> OpExpr
  | OE_Str  : string -> OpExpr.

(* ------------------------------------------------------------------ *)
(**  2.  Lex term syntax (admissible fragment, constant head).        *)
(* ------------------------------------------------------------------ *)

(** The admissible Lex fragment restricted to the constant head
    constructor over scalar values. *)

Inductive LexTerm : Type :=
  | LT_Const : LexValue -> LexTerm.

(* ------------------------------------------------------------------ *)
(**  3.  The compilation function, scalar constant case.              *)
(* ------------------------------------------------------------------ *)

(** Value lifting. Mirrors the scalar cases of the Rust reference in
    [crates/op-lex-compiler/src/lift.rs]. *)

Definition lift_value (v : LexValue) : OpExpr :=
  match v with
  | LV_Unit    => OE_Unit
  | LV_Bool b  => OE_Bool b
  | LV_Int n   => OE_Int n
  | LV_Str s   => OE_Str s
  end.

(** The compilation function on the admissible fragment, restricted
    to the constant head constructor. Mirrors the Rust
    [compile_const] in [crates/op-lex-compiler/src/case_const.rs]. *)

Definition compile (t : LexTerm) : OpExpr :=
  match t with
  | LT_Const v => lift_value v
  end.

(** Reflection: the inverse of [lift_value] on its image. *)

Definition reflect_op (e : OpExpr) : LexValue :=
  match e with
  | OE_Unit   => LV_Unit
  | OE_Bool b => LV_Bool b
  | OE_Int n  => LV_Int n
  | OE_Str s  => LV_Str s
  end.

(** A direct structural identity: [reflect_op] cancels [lift_value]. *)

Lemma reflect_lift : forall v, reflect_op (lift_value v) = v.
Proof. intros [ | b | n | s ]; reflexivity. Qed.

Lemma lift_reflect : forall e, lift_value (reflect_op e) = e.
Proof. intros [ | b | n | s ]; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(**  4.  Trace labels.                                                *)
(* ------------------------------------------------------------------ *)

(** A trace emits either a silent [tau] step or an observable
    verdict. For the scalar constant case, no silent prefix is
    required: the verdict is the embedded value, observed on the
    single reduction step that exhibits the term as a value. The
    [tau] label is retained in the alphabet because later cases
    (hole-fill especially) produce silent attestation-append
    transitions before the observable emit. *)

Inductive Label : Type :=
  | LTau  : Label
  | LEmit : LexValue -> Label.

(* ------------------------------------------------------------------ *)
(**  5.  Small-step operational semantics.                            *)
(* ------------------------------------------------------------------ *)

(** Lex reduction. The constant rule says a [LT_Const v] exhibits
    the value [v] on a single observable step. We model this as a
    one-step emission that stabilizes the term. *)

Inductive lex_step : LexTerm -> Label -> LexTerm -> Prop :=
  | LexStepConst :
      forall v, lex_step (LT_Const v) (LEmit v) (LT_Const v).

(** Op reduction. Each scalar Op literal exhibits the corresponding
    [LexValue] in a single observable step. The four constructors
    below are in bijection with the four scalar cases of
    [LexValue]. *)

Inductive op_step : OpExpr -> Label -> OpExpr -> Prop :=
  | OpStepUnit :
      op_step OE_Unit (LEmit LV_Unit) OE_Unit
  | OpStepBool :
      forall b, op_step (OE_Bool b) (LEmit (LV_Bool b)) (OE_Bool b)
  | OpStepInt :
      forall n, op_step (OE_Int n) (LEmit (LV_Int n)) (OE_Int n)
  | OpStepStr :
      forall s, op_step (OE_Str s) (LEmit (LV_Str s)) (OE_Str s).

(* ------------------------------------------------------------------ *)
(**  6.  Verdict predicates.                                          *)
(* ------------------------------------------------------------------ *)

Definition lex_verdict (t : LexTerm) (v : LexValue) : Prop :=
  exists t', lex_step t (LEmit v) t'.

Definition op_verdict (e : OpExpr) (v : LexValue) : Prop :=
  exists e', op_step e (LEmit v) e'.

(* ------------------------------------------------------------------ *)
(**  7.  Key operational lemma: lifting emits the source value.      *)
(* ------------------------------------------------------------------ *)

(** For every scalar [v], the lifted Op expression emits [v]. *)

Lemma lift_value_emits : forall v, op_step (lift_value v) (LEmit v) (lift_value v).
Proof.
  intros [ | b | n | s ]; simpl; constructor.
Qed.

(** Converse: if the lifted expression emits [w], then [w = v]. *)

Lemma lift_value_emits_unique :
  forall v w e',
    op_step (lift_value v) (LEmit w) e' ->
    w = v.
Proof.
  intros v w e' H.
  destruct v as [ | b | n | s ]; simpl in H; inversion H; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(**  8.  Verdict preservation for the scalar constant case.           *)
(* ------------------------------------------------------------------ *)

(** Forward direction: the Lex constant verdict is preserved by
    compilation. *)

Theorem verdict_preservation_const_forward :
  forall v vv,
    lex_verdict (LT_Const v) vv ->
    op_verdict (compile (LT_Const v)) vv.
Proof.
  intros v vv [t' Hstep].
  inversion Hstep; subst.
  simpl. exists (lift_value vv). apply lift_value_emits.
Qed.

(** Backward direction: the Op verdict of a compiled constant
    coincides with the Lex verdict of the source constant. *)

Theorem verdict_preservation_const_backward :
  forall v vv,
    op_verdict (compile (LT_Const v)) vv ->
    lex_verdict (LT_Const v) vv.
Proof.
  intros v vv [e' Hstep].
  simpl in Hstep.
  pose proof (@lift_value_emits_unique v vv e' Hstep) as Heq.
  subst vv.
  exists (LT_Const v). constructor.
Qed.

(** The combined biconditional — the Lex and Op verdicts coincide
    for every scalar Lex constant. *)

Theorem verdict_preservation_const :
  forall v vv,
    lex_verdict (LT_Const v) vv <->
    op_verdict (compile (LT_Const v)) vv.
Proof.
  intros v vv. split.
  - apply verdict_preservation_const_forward.
  - apply verdict_preservation_const_backward.
Qed.

(** The stronger concrete form: for every scalar [v], the verdict
    in both languages is exactly [v]. *)

Theorem const_verdict_is_value :
  forall v,
    lex_verdict (LT_Const v) v /\
    op_verdict (compile (LT_Const v)) v.
Proof.
  intros v. split.
  - exists (LT_Const v). constructor.
  - simpl. exists (lift_value v). apply lift_value_emits.
Qed.

(** Determinism: the constant verdict is unique in both languages. *)

Theorem lex_const_verdict_unique :
  forall v va vb,
    lex_verdict (LT_Const v) va ->
    lex_verdict (LT_Const v) vb ->
    va = vb.
Proof.
  intros v va vb [ta Ha] [tb Hb].
  inversion Ha; subst. inversion Hb; subst. reflexivity.
Qed.

Theorem op_const_verdict_unique :
  forall v va vb,
    op_verdict (compile (LT_Const v)) va ->
    op_verdict (compile (LT_Const v)) vb ->
    va = vb.
Proof.
  intros v va vb [ea Ha] [eb Hb].
  simpl in Ha, Hb.
  pose proof (@lift_value_emits_unique v va ea Ha) as Heqa.
  pose proof (@lift_value_emits_unique v vb eb Hb) as Heqb.
  subst va. subst vb. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(**  9.  Proof obligations.                                           *)
(* ------------------------------------------------------------------ *)

(** The §6.2 compilation function comprises six cases. The scalar
    shape of the constant case is closed above. The remaining
    obligations are registered below as [Admitted.] theorems
    carrying the signature of the target result and a
    proof-structure comment.

    The shapes introduced here as parameters mirror the Rust AST
    extensions in [crates/op-lex-compiler/src/ast.rs]. A follow-on
    file replaces each [Parameter] with the corresponding
    [Inductive] definition and discharges the [Admitted.]
    statements. *)

Section Obligations.

  (** Parameters carried across this obligations section. Each
      follow-on refinement replaces these with concrete syntactic
      definitions (records, lists, variants; variable references;
      match expressions; defeasible rules; sanctions dominance;
      filled holes) taken from the Rust reference. *)

  Parameter ExtLexTerm     : Type.
  Parameter ExtOpExpr      : Type.
  Parameter ExtCompile     : ExtLexTerm -> ExtOpExpr.
  Parameter ExtLexVerdict  : ExtLexTerm -> LexValue -> Prop.
  Parameter ExtOpVerdict   : ExtOpExpr  -> LexValue -> Prop.

  Parameter ELV_Record  : list (string * LexValue) -> LexValue.
  Parameter ELV_List    : list LexValue -> LexValue.
  Parameter ELV_Variant : string -> LexValue -> LexValue.
  Parameter ELT_Const   : LexValue -> ExtLexTerm.

  Parameter ELT_Var        : string -> ExtLexTerm.
  Parameter ELT_Match      : ExtLexTerm -> list (string * string * ExtLexTerm) -> ExtLexTerm.
  Parameter ELT_Defeasible : string -> ExtLexTerm -> list (ExtLexTerm * ExtLexTerm * nat * nat) -> ExtLexTerm.
  Parameter ELT_Sanctions  : ExtLexTerm -> ExtLexTerm.
  Parameter ELT_HoleFill   : string -> ExtLexTerm -> ExtLexTerm.

  (** ** Constant case — record / list / variant shapes.

      Goal. Verdict preservation extends to record, list, and
      variant constructors.

      Proof strategy. Structural induction on the [LexValue]
      constructor, with a nested induction on the list of fields
      (record case) and on the list of elements (list case). The
      inductive step uses the scalar base cases proved above. *)

  Theorem verdict_preservation_const_record :
    forall (fields : list (string * LexValue)) (vv : LexValue),
      ExtLexVerdict (ELT_Const (ELV_Record fields)) vv <->
      ExtOpVerdict  (ExtCompile (ELT_Const (ELV_Record fields))) vv.
  Proof. Admitted.

  Theorem verdict_preservation_const_list :
    forall (elems : list LexValue) (vv : LexValue),
      ExtLexVerdict (ELT_Const (ELV_List elems)) vv <->
      ExtOpVerdict  (ExtCompile (ELT_Const (ELV_List elems))) vv.
  Proof. Admitted.

  Theorem verdict_preservation_const_variant :
    forall (tag : string) (payload : LexValue) (vv : LexValue),
      ExtLexVerdict (ELT_Const (ELV_Variant tag payload)) vv <->
      ExtOpVerdict  (ExtCompile (ELT_Const (ELV_Variant tag payload))) vv.
  Proof. Admitted.

  (** ** Variable case.

      Goal. For every prelude-bound variable name resolving to a
      [LexValue], the compiled image emits that value iff the Lex
      variable emits it.

      Proof strategy. The variable case has no recursive term
      structure. Introduce a prelude-lookup relation as a
      parameter; the proof reduces to the scalar constant case
      once the lookup equation is rewritten. *)

  Theorem verdict_preservation_var :
    forall (name : string) (resolved : LexValue),
      ExtLexVerdict (ELT_Var name) resolved <->
      ExtOpVerdict  (ExtCompile (ELT_Var name)) resolved.
  Proof. Admitted.

  (** ** Match case.

      Goal. For every match term with scrutinee [s] and branch
      list [bs], the compiled image (an Op match against the
      lifted scrutinee with a materialized fail-closed
      catch-all) emits verdict [vv] iff the Lex match emits
      [vv].

      Proof strategy. Induction on the branch list, using the
      constant lemma as the base when each branch body reduces
      to a literal. Uniqueness of the matched branch closes the
      inductive step. *)

  Theorem verdict_preservation_match :
    forall (scrutinee : ExtLexTerm)
           (branches : list (string * string * ExtLexTerm))
           (vv : LexValue),
      ExtLexVerdict (ELT_Match scrutinee branches) vv <->
      ExtOpVerdict  (ExtCompile (ELT_Match scrutinee branches)) vv.
  Proof. Admitted.

  (** ** Defeasible case.

      Goal. For every defeasible rule with base body [b] and
      exception list [exs], the compiled image (nested guarded
      matches sorted by priority descending then source_position
      ascending) emits verdict [vv] iff the Lex rule emits [vv].

      Proof strategy. Well-founded induction on the lexicographic
      order on (priority, source_position). The base body is the
      fallback when no guard fires. *)

  Theorem verdict_preservation_defeasible :
    forall (rule_name : string)
           (base : ExtLexTerm)
           (exceptions : list (ExtLexTerm * ExtLexTerm * nat * nat))
           (vv : LexValue),
      ExtLexVerdict (ELT_Defeasible rule_name base exceptions) vv <->
      ExtOpVerdict  (ExtCompile (ELT_Defeasible rule_name base exceptions)) vv.
  Proof. Admitted.

  (** ** Sanctions-dominance case.

      Goal. For every sanctions-dominance rule, the compiled image
      (a host call to [sanctions.check] with the lifted principal)
      emits the same two-valued verdict ({Compliant,
      SanctionsBlocked}) that the Lex evaluator emits given the
      same host response.

      Proof strategy. Axiomatize the host [sanctions.check]
      primitive as a deterministic function from principals to the
      two-element verdict set; a single case-split on the host
      response closes the case. *)

  Theorem verdict_preservation_sanctions :
    forall (principal : ExtLexTerm) (vv : LexValue),
      ExtLexVerdict (ELT_Sanctions principal) vv <->
      ExtOpVerdict  (ExtCompile (ELT_Sanctions principal)) vv.
  Proof. Admitted.

  (** ** Hole-fill case — the §6.3 bisimulation up to [tau].

      Goal. For every filled discretion hole, the compiled image
      emits verdict [vv] iff the Lex fill emits [vv]. The Op
      trace is the Lex trace preceded by exactly one
      [tau]-labelled attestation-append step.

      Proof strategy. A weak bisimulation pairs each Lex state
      with the Op state obtained by unwinding one [tau]-labelled
      attestation-append transition. The relation is closed under
      subsequent observable emissions. Conclude by coinduction. *)

  Theorem verdict_preservation_fill :
    forall (hole_id : string) (filler : ExtLexTerm) (vv : LexValue),
      ExtLexVerdict (ELT_HoleFill hole_id filler) vv <->
      ExtOpVerdict  (ExtCompile (ELT_HoleFill hole_id filler)) vv.
  Proof. Admitted.

End Obligations.

(* ------------------------------------------------------------------ *)
(**  10.  End-to-end sanity examples.                                *)
(* ------------------------------------------------------------------ *)

Example const_bool_true_verdict :
  lex_verdict (LT_Const (LV_Bool true)) (LV_Bool true).
Proof. exists (LT_Const (LV_Bool true)). constructor. Qed.

Example const_int_42_compiles_and_reduces :
  op_verdict (compile (LT_Const (LV_Int 42))) (LV_Int 42).
Proof. exists (OE_Int 42). constructor. Qed.

Example const_str_hello_round_trip :
  lex_verdict (LT_Const (LV_Str "hello")) (LV_Str "hello") /\
  op_verdict (compile (LT_Const (LV_Str "hello"))) (LV_Str "hello").
Proof.
  split.
  - exists (LT_Const (LV_Str "hello")). constructor.
  - exists (OE_Str "hello"). constructor.
Qed.

Example const_unit_round_trip :
  lex_verdict (LT_Const LV_Unit) LV_Unit /\
  op_verdict (compile (LT_Const LV_Unit)) LV_Unit.
Proof.
  split.
  - exists (LT_Const LV_Unit). constructor.
  - exists OE_Unit. constructor.
Qed.

(* ------------------------------------------------------------------ *)
(**  End of file.                                                    *)
(* ------------------------------------------------------------------ *)
