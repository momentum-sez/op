(** * CompilationSoundness.v

    Mechanization of verdict preservation for the compilation function
    [[.]] : Lex -> Op.

    Nine cases are mechanized and closed with [Qed.]:

      1. Scalar constant case (§6.2).
      2. Sanctions-dominance case (§6.2 / §6.3).
      3. Variable case (§6.2), against a shared prelude parameter.
      4. Constant case — record shape (§6.2), restricted to records
         whose field values are scalars.
      5. Constant case — list shape (§6.2), restricted to lists
         whose elements are scalars.
      6. Constant case — variant shape (§6.2), restricted to
         variants whose payload is a scalar.
      7. Match case (§6.2), restricted to scalar scrutinees and
         scalar branch bodies.
      8. Defeasible case (§6.2), restricted to scalar bases,
         boolean guards, and scalar exception bodies.
      9. Hole-fill case (§6.3), closed by weak simulation up to
         [tau]-labelled attestation append.

    Scope.

      - Lex AST (admissible fragment, constant head constructor,
        scalar payloads; plus sanctions-dominance head for case 2;
        plus constant/variable heads for case 3; plus record-constant
        head for case 4; plus list-constant head for case 5; plus
        variant-constant head for case 6)
      - Op AST (expression fragment sufficient for lifted scalar
        constants; plus host-call form for case 2; plus
        literal/variable forms for case 3; plus record form for
        case 4; plus list form for case 5; plus variant form for
        case 6)
      - value-lifting function [lift_value : LexValue -> OpExpr]
      - compilation functions [compile : LexTerm -> OpExpr],
        [sanct_compile], [var_compile], [rec_compile],
        [list_compile], [variant_compile], [match_compile],
        [def_compile], [fill_compile]
      - small-step operational semantics for Lex and Op with a trace
        alphabet distinguishing silent [tau] transitions from
        observable verdict emissions; the record, list, and variant
        cases use bespoke emission payloads (field list, element
        list, and tag-payload pair respectively)
      - verdict-extraction predicates on Lex terms and Op expressions
      - the verdict-preservation theorems for the nine mechanized
        cases, proved in both directions
*)

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
    the record, list, and variant shapes are mechanized in
    §§11–13 below. *)

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
(**  9.  Sanctions-dominance case.                                    *)
(* ------------------------------------------------------------------ *)

(** The §6.2 sanctions-dominance rule:

      [[SanctionsDominance(p)]]  =
        call("sanctions.check", { principal: [[p]] })

    The host primitive [sanctions.check] returns a two-valued verdict
    drawn from the set [{Compliant, SanctionsBlocked}]. The
    sanctions-bottom semantics — a sanctions-blocked principal
    dominates every other verdict in the residual pipeline — is
    enforced in the host, not in the compiler. The compiler
    guarantees that any path reaching a committing effect in the
    compiled program is dominated by a [sanctions.check] invocation;
    see §3.9 of the Op language reference.

    Mechanization strategy. Introduce a concrete Lex head for
    sanctions-dominance applied to a scalar principal, a concrete Op
    host-call form with a single named argument, a deterministic
    axiomatic host [host_sanctions] with a two-element range, and
    small-step reductions on both sides that thread the principal
    through the host before emitting the verdict. Verdict
    preservation reduces to a single case-split on the host response
    once the principal has emitted its scalar value. *)

(** Concrete Lex head for a sanctions-dominance rule applied to a
    scalar principal. *)

Inductive SanctLexTerm : Type :=
  | SLT_Const     : LexValue -> SanctLexTerm
  | SLT_Sanctions : SanctLexTerm -> SanctLexTerm.

(** Concrete Op form for a host call with a single named argument
    ([principal]). The scalar literal case wraps the base [OpExpr]. *)

Inductive SanctOpExpr : Type :=
  | SOE_Lit  : OpExpr -> SanctOpExpr
  | SOE_Call : string -> SanctOpExpr -> SanctOpExpr.

(** Host primitive. Parameterized as a deterministic function from
    principals to the verdict lattice; production wiring supplies a
    concrete implementation bound to the sanctions backend.

    The two-valued range obligation is NOT a file-level [Axiom]: it is
    a [Hypothesis] on the sanity-check Example below, scoped to the
    [SanctionsRangeSanity] Section so that any consumer of the Example
    must discharge the obligation with a proof for the host they are
    binding.  The main preservation theorem
    [verdict_preservation_sanctions] depends only on the shared-model
    parameter [host_sanctions] itself and carries no range
    obligation. *)

Parameter host_sanctions : LexValue -> LexValue.

(** Lex reduction for the sanctions head. A [SLT_Const v_p] emits its
    scalar [v_p] in one observable step; [SLT_Sanctions p] emits
    [host_sanctions v_p] once [p] has emitted [v_p]. *)

Inductive sanct_lex_step : SanctLexTerm -> Label -> SanctLexTerm -> Prop :=
  | SLexStepConst :
      forall v,
        sanct_lex_step (SLT_Const v) (LEmit v) (SLT_Const v)
  | SLexStepSanctions :
      forall p v_p,
        sanct_lex_step p (LEmit v_p) p ->
        sanct_lex_step (SLT_Sanctions p) (LEmit (host_sanctions v_p)) (SLT_Sanctions p).

(** Op reduction for the sanctions host call. [SOE_Lit (lift_value v_p)]
    emits [v_p]; [SOE_Call "sanctions.check" e_p] emits
    [host_sanctions v_p] once [e_p] has emitted [v_p]. *)

Inductive sanct_op_step : SanctOpExpr -> Label -> SanctOpExpr -> Prop :=
  | SOpStepLit :
      forall v,
        sanct_op_step (SOE_Lit (lift_value v)) (LEmit v) (SOE_Lit (lift_value v))
  | SOpStepCall :
      forall e_p v_p,
        sanct_op_step e_p (LEmit v_p) e_p ->
        sanct_op_step (SOE_Call "sanctions.check" e_p)
                      (LEmit (host_sanctions v_p))
                      (SOE_Call "sanctions.check" e_p).

(** Compilation, sanctions fragment. Mirrors the Rust reference in
    [crates/op-lex-compiler/src/case_sanctions.rs]. *)

Fixpoint sanct_compile (t : SanctLexTerm) : SanctOpExpr :=
  match t with
  | SLT_Const v       => SOE_Lit (lift_value v)
  | SLT_Sanctions p   => SOE_Call "sanctions.check" (sanct_compile p)
  end.

Definition sanct_lex_verdict (t : SanctLexTerm) (v : LexValue) : Prop :=
  exists t', sanct_lex_step t (LEmit v) t'.

Definition sanct_op_verdict (e : SanctOpExpr) (v : LexValue) : Prop :=
  exists e', sanct_op_step e (LEmit v) e'.

(** Helper. Compilation of the sanctions head unfolds to a host call
    on the compiled principal. *)

Lemma compile_sanctions_shape :
  forall p,
    sanct_compile (SLT_Sanctions p) =
    SOE_Call "sanctions.check" (sanct_compile p).
Proof. intros p. reflexivity. Qed.

(** Helper. The Lex emission of a scalar constant under the sanctions
    fragment is uniquely the embedded value. *)

Lemma sanct_lex_const_emit_unique :
  forall v w t',
    sanct_lex_step (SLT_Const v) (LEmit w) t' ->
    w = v.
Proof. intros v w t' H. inversion H; reflexivity. Qed.

(** Helper. [lift_value] is injective on [LexValue]. *)

Lemma lift_value_inj :
  forall v w, lift_value v = lift_value w -> v = w.
Proof.
  intros v w Heq.
  assert (Heq' : reflect_op (lift_value v) = reflect_op (lift_value w))
    by (rewrite Heq; reflexivity).
  rewrite reflect_lift, reflect_lift in Heq'.
  exact Heq'.
Qed.

(** Helper. The Op emission of a [SOE_Lit (lift_value v)] is uniquely
    the embedded value. *)

Lemma sanct_op_lit_emit_unique :
  forall v w e',
    sanct_op_step (SOE_Lit (lift_value v)) (LEmit w) e' ->
    w = v.
Proof.
  intros v w e' H.
  inversion H; subst.
  apply lift_value_inj in H1.
  exact H1.
Qed.

(** Verdict preservation for the sanctions-dominance case, restricted
    to a scalar-constant principal. The principal assumption mirrors
    the admissible-fragment restriction used throughout §6.2: every
    rule position accepts a value shape, with deeper term structure
    delivered by earlier compilation cases. *)

Theorem verdict_preservation_sanctions :
  forall (v_p : LexValue) (vv : LexValue),
    sanct_lex_verdict (SLT_Sanctions (SLT_Const v_p)) vv <->
    sanct_op_verdict  (sanct_compile (SLT_Sanctions (SLT_Const v_p))) vv.
Proof.
  intros v_p vv. split.
  - (* Forward. The Lex step fixes vv = host_sanctions v_p; the Op
       side builds the matching call trace. *)
    intros [t' Hstep].
    inversion Hstep; subst.
    (* The principal substep SLexStepConst fixes the emitted scalar. *)
    match goal with
    | [ Hp : sanct_lex_step (SLT_Const v_p) (LEmit ?w) _ |- _ ] =>
        apply sanct_lex_const_emit_unique in Hp; subst w
    end.
    simpl.
    exists (SOE_Call "sanctions.check" (SOE_Lit (lift_value v_p))).
    apply SOpStepCall.
    apply SOpStepLit.
  - (* Backward. The Op call step fixes vv = host_sanctions v_p; the
       Lex side mirrors the emission. *)
    intros [e' Hstep].
    simpl in Hstep.
    inversion Hstep; subst.
    match goal with
    | [ Hp : sanct_op_step (SOE_Lit (lift_value v_p)) (LEmit ?w) _ |- _ ] =>
        apply sanct_op_lit_emit_unique in Hp; subst w
    end.
    exists (SLT_Sanctions (SLT_Const v_p)).
    apply SLexStepSanctions.
    apply SLexStepConst.
Qed.

(** Sanity. The verdict is always one of the two host outputs.
    Scoped to a Section that takes the two-valued range as an
    explicit [Hypothesis]; the Example's signature after the Section
    closes therefore universally quantifies the range proof, so any
    consumer must discharge it with a proof for the concrete host
    they are binding. *)

Section SanctionsRangeSanity.

Hypothesis host_sanctions_range :
  forall p,
    host_sanctions p = LV_Str "Compliant" \/
    host_sanctions p = LV_Str "SanctionsBlocked".

Example sanctions_verdict_is_two_valued :
  forall v_p,
    sanct_lex_verdict (SLT_Sanctions (SLT_Const v_p)) (LV_Str "Compliant") \/
    sanct_lex_verdict (SLT_Sanctions (SLT_Const v_p)) (LV_Str "SanctionsBlocked").
Proof.
  intros v_p.
  destruct (host_sanctions_range v_p) as [Hc | Hb].
  - left.  exists (SLT_Sanctions (SLT_Const v_p)). rewrite <- Hc.
    apply SLexStepSanctions. constructor.
  - right. exists (SLT_Sanctions (SLT_Const v_p)). rewrite <- Hb.
    apply SLexStepSanctions. constructor.
Qed.

End SanctionsRangeSanity.

(* ------------------------------------------------------------------ *)
(**  10.  Variable case.                                              *)
(* ------------------------------------------------------------------ *)

(** The §6.2 variable compilation rule:

      [[Var n]]  =  OpVar n

    A variable reference evaluates by looking the name up in a
    deterministic prelude shared by both Lex and Op. The prelude is
    axiomatized as a total function into [option LexValue]; an
    unbound name yields [None] and no emission fires. Both languages
    perform the same lookup, so the preservation proof reduces to
    the determinism of the shared prelude.

    Mechanization strategy. Introduce a concrete Lex term with both
    constant and variable forms, an Op expression with matching
    constant-literal and variable-reference forms, a parameterized
    prelude, and small-step reductions that emit the looked-up value
    on each side. The compilation function maps [VLT_Var n] to
    [VOE_Var n] and lifts constants as before. *)

(** Concrete Lex head for the variable fragment. [VLT_Const] embeds
    the scalar constant layer; [VLT_Var n] names a prelude entry. *)

Inductive VarLexTerm : Type :=
  | VLT_Const : LexValue -> VarLexTerm
  | VLT_Var   : string   -> VarLexTerm.

(** Concrete Op form for the variable fragment. [VOE_Lit] receives a
    lifted constant; [VOE_Var n] performs the runtime prelude lookup
    on the Op side. *)

Inductive VarOpExpr : Type :=
  | VOE_Lit : OpExpr -> VarOpExpr
  | VOE_Var : string -> VarOpExpr.

(** Prelude. Axiomatized as a deterministic partial function shared
    by both Lex and Op. [prelude n = Some v] means the name [n] is
    bound to the scalar [v] in the runtime environment active at
    compile time; [prelude n = None] means [n] is unbound. Both
    languages read from this same parameter, so the semantics agree
    on every name. *)

Parameter prelude : string -> option LexValue.

(** Lex reduction for the variable fragment. A [VLT_Const v] emits
    [v] in one step; a [VLT_Var n] emits the looked-up value when
    [prelude n = Some v], and is stuck otherwise (no emission
    rule). *)

Inductive var_lex_step : VarLexTerm -> Label -> VarLexTerm -> Prop :=
  | VLexStepConst :
      forall v,
        var_lex_step (VLT_Const v) (LEmit v) (VLT_Const v)
  | VLexStepVar :
      forall n v,
        prelude n = Some v ->
        var_lex_step (VLT_Var n) (LEmit v) (VLT_Var n).

(** Op reduction for the variable fragment. Mirrors the Lex rules
    against the same prelude parameter. *)

Inductive var_op_step : VarOpExpr -> Label -> VarOpExpr -> Prop :=
  | VOpStepLit :
      forall v,
        var_op_step (VOE_Lit (lift_value v)) (LEmit v) (VOE_Lit (lift_value v))
  | VOpStepVar :
      forall n v,
        prelude n = Some v ->
        var_op_step (VOE_Var n) (LEmit v) (VOE_Var n).

(** Compilation, variable fragment. Mirrors the Rust reference in
    [crates/op-lex-compiler/src/case_var.rs]. *)

Definition var_compile (t : VarLexTerm) : VarOpExpr :=
  match t with
  | VLT_Const v => VOE_Lit (lift_value v)
  | VLT_Var n   => VOE_Var n
  end.

Definition var_lex_verdict (t : VarLexTerm) (v : LexValue) : Prop :=
  exists t', var_lex_step t (LEmit v) t'.

Definition var_op_verdict (e : VarOpExpr) (v : LexValue) : Prop :=
  exists e', var_op_step e (LEmit v) e'.

(** Helper. Compilation of a variable unfolds to a variable
    reference in Op. *)

Lemma var_compile_shape_var :
  forall n, var_compile (VLT_Var n) = VOE_Var n.
Proof. intros n. reflexivity. Qed.

(** Verdict preservation for the variable case. Both directions
    follow by a case split on [prelude n]; the shared prelude forces
    the emitted value on each side to agree. *)

Theorem verdict_preservation_var :
  forall (n : string) (vv : LexValue),
    var_lex_verdict (VLT_Var n) vv <->
    var_op_verdict  (var_compile (VLT_Var n)) vv.
Proof.
  intros n vv. split.
  - (* Forward. *)
    intros [t' Hstep].
    inversion Hstep; subst.
    rewrite var_compile_shape_var.
    exists (VOE_Var n).
    apply VOpStepVar. assumption.
  - (* Backward. *)
    intros [e' Hstep].
    rewrite var_compile_shape_var in Hstep.
    inversion Hstep; subst.
    exists (VLT_Var n).
    apply VLexStepVar. assumption.
Qed.

(** Verdict preservation extends to the constant shape within the
    variable fragment, recovering the scalar-constant result. *)

(** Helper. The Op emission of a [VOE_Lit (lift_value v)] is uniquely
    the embedded value. *)

Lemma var_op_lit_emit_unique :
  forall v w e',
    var_op_step (VOE_Lit (lift_value v)) (LEmit w) e' ->
    w = v.
Proof.
  intros v w e' H.
  inversion H; subst.
  apply lift_value_inj in H1.
  exact H1.
Qed.

Theorem verdict_preservation_var_const :
  forall (v : LexValue) (vv : LexValue),
    var_lex_verdict (VLT_Const v) vv <->
    var_op_verdict  (var_compile (VLT_Const v)) vv.
Proof.
  intros v vv. split.
  - intros [t' Hstep]. inversion Hstep; subst.
    simpl. exists (VOE_Lit (lift_value vv)).
    apply VOpStepLit.
  - intros [e' Hstep]. simpl in Hstep.
    pose proof (@var_op_lit_emit_unique v vv e' Hstep) as Heq.
    subst vv.
    exists (VLT_Const v). apply VLexStepConst.
Qed.

(* ------------------------------------------------------------------ *)
(**  11.  Constant case — record shape.                               *)
(* ------------------------------------------------------------------ *)

(** The §6.2 constant-case extension to records with scalar fields:

      [[Const (Record [(k_i, v_i)])]]  =  OpRecord [(k_i, lift v_i)]

    The Lex term emits the record value in one observable step. The
    Op expression emits the record value once every field's compiled
    image has emitted its scalar. Structural induction on the field
    list closes both directions, with the scalar-constant lemma
    discharging each field's base case. *)

(** Concrete Lex head for the record fragment. Restricted to a
    record-valued constant; the fields carry scalar [LexValue]s. *)

Inductive RecLexTerm : Type :=
  | RLT_ConstRec : list (string * LexValue) -> RecLexTerm.

(** Concrete Op form for the record fragment. [ROE_Record] holds a
    list of (key, compiled-field) pairs; each compiled field is a
    lifted scalar. *)

Inductive RecOpExpr : Type :=
  | ROE_Record : list (string * OpExpr) -> RecOpExpr.

(** Lex reduction for the record fragment. A record-valued constant
    emits the record value in one step. The emission payload is the
    field list itself; the surrounding framework's [Label] alphabet
    only carries scalar verdicts, so the record emission uses a
    bespoke relation taking [list (string * LexValue)] directly. *)

Inductive rec_lex_step : RecLexTerm -> list (string * LexValue) -> RecLexTerm -> Prop :=
  | RLexStepRec :
      forall fields,
        rec_lex_step (RLT_ConstRec fields) fields (RLT_ConstRec fields).

(** Op field-list reduction. Each field's compiled image emits its
    source scalar. The relation is a straight pointwise predicate on
    the zipped list of Lex fields and Op fields. *)

Inductive op_fields_emit : list (string * OpExpr) -> list (string * LexValue) -> Prop :=
  | FieldsEmitNil :
      op_fields_emit nil nil
  | FieldsEmitCons :
      forall k v rest_op rest_lex,
        op_fields_emit rest_op rest_lex ->
        op_fields_emit ((k, lift_value v) :: rest_op) ((k, v) :: rest_lex).

(** Op reduction for the record fragment. A compiled record emits
    the list of source scalars once the pointwise field relation
    holds. *)

Inductive rec_op_step : RecOpExpr -> list (string * LexValue) -> RecOpExpr -> Prop :=
  | ROpStepRecord :
      forall op_fields lex_fields,
        op_fields_emit op_fields lex_fields ->
        rec_op_step (ROE_Record op_fields) lex_fields (ROE_Record op_fields).

(** Compilation, record fragment. Mirrors the Rust reference in
    [crates/op-lex-compiler/src/case_const.rs] for the record shape:
    every field's value is lifted pointwise. *)

Definition rec_compile (t : RecLexTerm) : RecOpExpr :=
  match t with
  | RLT_ConstRec fields =>
      ROE_Record (map (fun (kv : string * LexValue) =>
                         let (k, v) := kv in (k, lift_value v)) fields)
  end.

Definition rec_lex_verdict (t : RecLexTerm) (fields : list (string * LexValue)) : Prop :=
  exists t', rec_lex_step t fields t'.

Definition rec_op_verdict (e : RecOpExpr) (fields : list (string * LexValue)) : Prop :=
  exists e', rec_op_step e fields e'.

(** Helper. For every list of scalar fields, the pointwise lifted
    Op field list emits the source list under [op_fields_emit]. Proof
    by induction on the field list; each step invokes the scalar
    lifting semantics once. *)

Lemma map_lift_value_emits :
  forall fields,
    op_fields_emit
      (map (fun (kv : string * LexValue) =>
              let (k, v) := kv in (k, lift_value v)) fields)
      fields.
Proof.
  induction fields as [ | [k v] rest IH].
  - simpl. apply FieldsEmitNil.
  - simpl. apply FieldsEmitCons. exact IH.
Qed.

(** Helper. Converse. If the pointwise lifted Op field list emits
    [lex_fields] under [op_fields_emit], then [lex_fields] is the
    original source list. Proof by induction on the
    [op_fields_emit] derivation, with injectivity of [lift_value]
    closing each field. *)

Lemma map_lift_value_emits_unique :
  forall fields lex_fields,
    op_fields_emit
      (map (fun (kv : string * LexValue) =>
              let (k, v) := kv in (k, lift_value v)) fields)
      lex_fields ->
    lex_fields = fields.
Proof.
  induction fields as [ | [k v] rest IH]; intros lex_fields H.
  - simpl in H. inversion H. reflexivity.
  - simpl in H. inversion H; subst.
    apply lift_value_inj in H2; subst v0.
    apply IH in H4; subst rest_lex.
    reflexivity.
Qed.

(** Verdict preservation for the record-shape constant case,
    restricted to records whose field values are scalars. The
    biconditional threads the pointwise field emission through
    [map_lift_value_emits] and [map_lift_value_emits_unique]. *)

Theorem verdict_preservation_const_record :
  forall (fields : list (string * LexValue)) (vv : list (string * LexValue)),
    rec_lex_verdict (RLT_ConstRec fields) vv <->
    rec_op_verdict  (rec_compile (RLT_ConstRec fields)) vv.
Proof.
  intros fields vv. split.
  - (* Forward. *)
    intros [t' Hstep].
    inversion Hstep; subst.
    simpl.
    eexists.
    apply ROpStepRecord.
    apply map_lift_value_emits.
  - (* Backward. *)
    intros [e' Hstep].
    simpl in Hstep.
    inversion Hstep; subst.
    apply map_lift_value_emits_unique in H0; subst vv.
    exists (RLT_ConstRec fields).
    apply RLexStepRec.
Qed.

(* ------------------------------------------------------------------ *)
(**  12.  Constant case — list shape.                                 *)
(* ------------------------------------------------------------------ *)

(** The §6.2 constant-case extension to list-valued constants with
    scalar elements:

      [[Const (List [v_i])]]  =  OpList [lift v_i]

    The Lex term emits the list value in one observable step. The Op
    expression emits the list value once every element's compiled
    image has emitted its scalar. The proof mirrors the record
    shape: structural induction on the element list, with the scalar
    lifting semantics discharging each element's base case. *)

(** Concrete Lex head for the list fragment. Restricted to a
    list-valued constant whose elements are scalar [LexValue]s. *)

Inductive ListLexTerm : Type :=
  | LLT_Const : list LexValue -> ListLexTerm.

(** Concrete Op form for the list fragment. [LOE_List] holds a list
    of compiled elements; each compiled element is a lifted scalar. *)

Inductive ListOpExpr : Type :=
  | LOE_List : list OpExpr -> ListOpExpr.

(** Lex reduction for the list fragment. A list-valued constant
    emits the element list in one step. As with the record case,
    the emission payload is a bespoke [list LexValue] in place of
    the surrounding framework's scalar alphabet. *)

Inductive list_lex_step : ListLexTerm -> list LexValue -> ListLexTerm -> Prop :=
  | LLexStepList :
      forall items,
        list_lex_step (LLT_Const items) items (LLT_Const items).

(** Op element-list emission relation. Each element's compiled image
    emits its source scalar. The relation is a pointwise predicate
    on the zipped list of Lex elements and Op elements. *)

Inductive op_items_emit : list OpExpr -> list LexValue -> Prop :=
  | ItemsEmitNil :
      op_items_emit nil nil
  | ItemsEmitCons :
      forall v rest_op rest_lex,
        op_items_emit rest_op rest_lex ->
        op_items_emit (lift_value v :: rest_op) (v :: rest_lex).

(** Op reduction for the list fragment. A compiled list emits the
    list of source scalars once the pointwise element relation
    holds. *)

Inductive list_op_step : ListOpExpr -> list LexValue -> ListOpExpr -> Prop :=
  | LOpStepList :
      forall op_items lex_items,
        op_items_emit op_items lex_items ->
        list_op_step (LOE_List op_items) lex_items (LOE_List op_items).

(** Compilation, list fragment. Mirrors the Rust reference in
    [crates/op-lex-compiler/src/case_const.rs] for the list shape:
    every element is lifted pointwise. *)

Definition list_compile (t : ListLexTerm) : ListOpExpr :=
  match t with
  | LLT_Const items => LOE_List (map lift_value items)
  end.

Definition list_lex_verdict (t : ListLexTerm) (items : list LexValue) : Prop :=
  exists t', list_lex_step t items t'.

Definition list_op_verdict (e : ListOpExpr) (items : list LexValue) : Prop :=
  exists e', list_op_step e items e'.

(** Helper. For every list of scalar elements, the pointwise lifted
    Op element list emits the source list under [op_items_emit].
    Proof by induction on the element list; each step invokes the
    scalar lifting semantics once. *)

Lemma list_lift_value_emits :
  forall items,
    op_items_emit (map lift_value items) items.
Proof.
  induction items as [ | v rest IH].
  - simpl. apply ItemsEmitNil.
  - simpl. apply ItemsEmitCons. exact IH.
Qed.

(** Helper. Converse. If the pointwise lifted Op element list emits
    [lex_items] under [op_items_emit], then [lex_items] is the
    original source list. Proof by induction on [items], with
    injectivity of [lift_value] closing each element. *)

Lemma list_lift_value_emits_unique :
  forall items lex_items,
    op_items_emit (map lift_value items) lex_items ->
    lex_items = items.
Proof.
  induction items as [ | v rest IH]; intros lex_items H.
  - simpl in H. inversion H. reflexivity.
  - simpl in H. inversion H; subst.
    apply lift_value_inj in H0; subst v0.
    apply IH in H3; subst rest_lex.
    reflexivity.
Qed.

(** Verdict preservation for the list-shape constant case,
    restricted to lists whose elements are scalars. The
    biconditional threads the pointwise element emission through
    [list_lift_value_emits] and [list_lift_value_emits_unique]. *)

Theorem verdict_preservation_const_list :
  forall (items : list LexValue) (vv : list LexValue),
    list_lex_verdict (LLT_Const items) vv <->
    list_op_verdict  (list_compile (LLT_Const items)) vv.
Proof.
  intros items vv. split.
  - (* Forward. *)
    intros [t' Hstep].
    inversion Hstep; subst.
    simpl.
    eexists.
    apply LOpStepList.
    apply list_lift_value_emits.
  - (* Backward. *)
    intros [e' Hstep].
    simpl in Hstep.
    inversion Hstep; subst.
    apply list_lift_value_emits_unique in H0; subst vv.
    exists (LLT_Const items).
    apply LLexStepList.
Qed.

(* ------------------------------------------------------------------ *)
(**  13.  Constant case — variant shape.                              *)
(* ------------------------------------------------------------------ *)

(** The §6.2 constant-case extension to variant-valued constants
    with a tag (string) and a scalar payload:

      [[Const (Variant tag v)]]  =  OpVariant tag (lift v)

    The Lex term emits the variant value in one observable step.
    The Op expression emits the variant value once the payload's
    compiled image has emitted its scalar. The proof is direct
    inversion on the single-step reductions, with the scalar
    [lift_value_emits] / [lift_value_emits_unique] lemmas closing
    the payload obligation. *)

(** Concrete Lex head for the variant fragment. Restricted to a
    variant-valued constant with a string tag and a scalar payload. *)

Inductive VarLT : Type :=
  | VLT_ConstVar : string -> LexValue -> VarLT.

(** Concrete Op form for the variant fragment. [VOE_Variant] holds
    the tag string and the lifted payload. *)

Inductive VarOE : Type :=
  | VOE_Variant : string -> OpExpr -> VarOE.

(** Lex reduction for the variant fragment. A variant-valued
    constant emits its (tag, payload) pair in one step. The
    emission payload is a [string * LexValue] pair, with a bespoke
    relation to carry it. *)

Inductive variant_lex_step : VarLT -> (string * LexValue) -> VarLT -> Prop :=
  | VarLexStepVariant :
      forall tag v,
        variant_lex_step (VLT_ConstVar tag v) (tag, v) (VLT_ConstVar tag v).

(** Op reduction for the variant fragment. A compiled variant emits
    its (tag, payload) pair once the payload's lifted image has
    emitted the scalar. The payload obligation is captured as a
    premise [op_step (lift_value v_op) (LEmit v) (lift_value v_op)]
    where [v_op] is the payload value; [lift_value_emits] discharges
    this premise. *)

Inductive variant_op_step : VarOE -> (string * LexValue) -> VarOE -> Prop :=
  | VarOpStepVariant :
      forall tag v,
        op_step (lift_value v) (LEmit v) (lift_value v) ->
        variant_op_step (VOE_Variant tag (lift_value v))
                        (tag, v)
                        (VOE_Variant tag (lift_value v)).

(** Compilation, variant fragment. Mirrors the Rust reference in
    [crates/op-lex-compiler/src/case_const.rs] for the variant
    shape: the tag carries through unchanged, the payload is
    lifted. *)

Definition variant_compile (t : VarLT) : VarOE :=
  match t with
  | VLT_ConstVar tag v => VOE_Variant tag (lift_value v)
  end.

Definition variant_lex_verdict (t : VarLT) (payload : string * LexValue) : Prop :=
  exists t', variant_lex_step t payload t'.

Definition variant_op_verdict (e : VarOE) (payload : string * LexValue) : Prop :=
  exists e', variant_op_step e payload e'.

(** Verdict preservation for the variant-shape constant case,
    restricted to variants whose payload is a scalar. Direct
    inversion on both sides; the scalar [lift_value_emits] and
    [lift_value_emits_unique] lemmas close the payload obligation. *)

Theorem verdict_preservation_const_variant :
  forall (tag : string) (v : LexValue) (vv : string * LexValue),
    variant_lex_verdict (VLT_ConstVar tag v) vv <->
    variant_op_verdict  (variant_compile (VLT_ConstVar tag v)) vv.
Proof.
  intros tag v vv. split.
  - (* Forward. *)
    intros [t' Hstep].
    inversion Hstep; subst.
    simpl.
    exists (VOE_Variant tag (lift_value v)).
    apply VarOpStepVariant.
    apply lift_value_emits.
  - (* Backward. *)
    intros [e' Hstep].
    simpl in Hstep.
    inversion Hstep; subst.
    apply lift_value_inj in H1; subst v0.
    exists (VLT_ConstVar tag v).
    apply VarLexStepVariant.
Qed.

(* ------------------------------------------------------------------ *)
(**  14.  Match case.                                                *)
(* ------------------------------------------------------------------ *)

(** The §6.2 match rule:

      [[match e { | C_i x_i => b_i }]]  =
        choose {
          when match(P_1, [[e]]) -> [[b_1]];
          ...;
          when match(P_n, [[e]]) -> [[b_n]];
          else fail-closed
        }

    Scope. The admissible fragment is restricted here to:

      - scalar-constant scrutinees ([LV_Unit] / [LV_Bool] / [LV_Int]
        / [LV_Str]);
      - finite nullary-constructor patterns, each identified with a
        scalar [LexValue] the scrutinee is compared against by
        syntactic equality;
      - scalar-constant branch bodies, so each compiled body is a
        lifted literal that emits its source value in one step;
      - fixed branch return type (the composed verdict [P]).

    Non-exhaustive match is supported: if no pattern matches, the
    Op expression emits the fail-closed sentinel
    [LV_Str "pattern_unmatched"], matching the Rust reference in
    [crates/op-lex-compiler/src/case_match.rs]. Dependent match
    (pattern binders introducing payload variables) is out of scope
    and will land in a follow-on extension once admissibility opens
    up non-nullary patterns.

    Mechanization strategy. A new [MatchLexTerm] / [MatchOpExpr]
    layer over the scalar-constant fragment. The scrutinee is a
    single scalar value; each branch is a (pattern, body) pair of
    scalar values. [match_compile] lifts the scrutinee and each
    branch body; the Op side carries the (lifted-pattern,
    lifted-body) pairs through a [MOE_Choose] node. Reduction on
    both sides walks the branch list in order; the first pattern
    equal to the scrutinee fires, delivering the branch body's
    value; if no pattern matches, both sides emit the fail-closed
    sentinel. Verdict preservation then follows by list induction
    over the branches: the scalar-constant lemma
    [lift_value_emits_unique] closes each base case; the inductive
    step uses [lift_value] injectivity to reduce pattern equality
    on the Op side to pattern equality on the Lex side. *)

(** Decidable equality on [LexValue]. Used for pattern matching. *)

Lemma LexValue_eq_dec : forall (v w : LexValue), {v = w} + {v <> w}.
Proof.
  decide equality.
  - apply Bool.bool_dec.
  - apply Z.eq_dec.
  - apply String.string_dec.
Defined.

(** Concrete Lex head for the match fragment. The scrutinee is a
    scalar value; the branch list pairs pattern values with body
    values. *)

Inductive MatchLexTerm : Type :=
  | MLT_Match : LexValue -> list (LexValue * LexValue) -> MatchLexTerm.

(** Concrete Op form for the match fragment. The compiled image is
    a choose-expression whose scrutinee is the lifted scalar and
    whose branches carry lifted pattern/body pairs. *)

Inductive MatchOpExpr : Type :=
  | MOE_Choose : OpExpr -> list (OpExpr * OpExpr) -> MatchOpExpr.

(** The fail-closed sentinel — a NonCompliant verdict tagged with
    [pattern_unmatched], mirroring the Rust
    [fail_closed_expr] in [case_match.rs]. The Coq mechanization
    uses a string-valued sentinel because the surrounding
    [LexValue] alphabet is scalar; the paper's fail-closed
    [Verdict::NonCompliant { reason: "pattern_unmatched" }] record
    lowers to this string under the scalar-only restriction. *)

Definition fail_closed_value : LexValue := LV_Str "pattern_unmatched".

(** Lex reduction for the match fragment. The first branch whose
    pattern equals the scrutinee fires, emitting the branch body.
    If no pattern matches, the fail-closed sentinel is emitted. The
    two rules are modelled as separate constructors indexed by the
    branch list prefix consumed. *)

Fixpoint lex_match_find (scrutinee : LexValue)
                        (branches : list (LexValue * LexValue))
                        : LexValue :=
  match branches with
  | nil => fail_closed_value
  | (p, b) :: rest =>
      if LexValue_eq_dec p scrutinee
      then b
      else lex_match_find scrutinee rest
  end.

Inductive match_lex_step : MatchLexTerm -> Label -> MatchLexTerm -> Prop :=
  | MLexStepMatch :
      forall scrutinee branches,
        match_lex_step
          (MLT_Match scrutinee branches)
          (LEmit (lex_match_find scrutinee branches))
          (MLT_Match scrutinee branches).

(** Op reduction for the match fragment. Mirrors the Lex semantics
    against the lifted scrutinee and lifted branch pairs. The
    branch traversal uses syntactic equality on [OpExpr], which
    agrees with scalar equality on [LexValue] via the injectivity
    of [lift_value]. *)

Fixpoint op_match_find (scrutinee : OpExpr)
                       (branches : list (OpExpr * OpExpr))
                       : OpExpr :=
  match branches with
  | nil => lift_value fail_closed_value
  | (p, b) :: rest =>
      match p, scrutinee with
      | OE_Unit, OE_Unit => b
      | OE_Bool b1, OE_Bool b2 => if Bool.bool_dec b1 b2 then b else op_match_find scrutinee rest
      | OE_Int n1, OE_Int n2 => if Z.eq_dec n1 n2 then b else op_match_find scrutinee rest
      | OE_Str s1, OE_Str s2 => if String.string_dec s1 s2 then b else op_match_find scrutinee rest
      | _, _ => op_match_find scrutinee rest
      end
  end.

Inductive match_op_step : MatchOpExpr -> Label -> MatchOpExpr -> Prop :=
  | MOpStepChoose :
      forall scrutinee branches v,
        op_step (op_match_find scrutinee branches) (LEmit v)
                (op_match_find scrutinee branches) ->
        match_op_step
          (MOE_Choose scrutinee branches)
          (LEmit v)
          (MOE_Choose scrutinee branches).

(** Compilation, match fragment. Mirrors the Rust reference in
    [crates/op-lex-compiler/src/case_match.rs] for the
    scalar-constant-scrutinee, nullary-pattern restriction: the
    scrutinee is lifted, each branch's pattern and body are
    lifted pointwise, the fail-closed catch-all is materialized
    implicitly by [op_match_find] returning
    [lift_value fail_closed_value] when the branch list is
    exhausted. *)

Definition match_compile (t : MatchLexTerm) : MatchOpExpr :=
  match t with
  | MLT_Match scrutinee branches =>
      MOE_Choose (lift_value scrutinee)
                 (map (fun (pb : LexValue * LexValue) =>
                         let (p, b) := pb in
                         (lift_value p, lift_value b)) branches)
  end.

Definition match_lex_verdict (t : MatchLexTerm) (v : LexValue) : Prop :=
  exists t', match_lex_step t (LEmit v) t'.

Definition match_op_verdict (e : MatchOpExpr) (v : LexValue) : Prop :=
  exists e', match_op_step e (LEmit v) e'.

(** Helper. The Op-side branch traversal, parameterized by the
    lifted scrutinee and the pointwise-lifted branch list, selects
    the lifted image of the Lex-side selection. By induction on
    the branch list; each step discriminates on whether the
    lifted pattern equals the lifted scrutinee and closes via
    injectivity of [lift_value]. *)

Lemma op_match_find_lifts :
  forall scrutinee branches,
    op_match_find (lift_value scrutinee)
                  (map (fun (pb : LexValue * LexValue) =>
                          let (p, b) := pb in
                          (lift_value p, lift_value b)) branches)
    = lift_value (lex_match_find scrutinee branches).
Proof.
  induction branches as [ | [p b] rest IH].
  - simpl. reflexivity.
  - simpl.
    destruct (LexValue_eq_dec p scrutinee) as [Heq | Hneq].
    + (* Patterns match: both sides select [b] / [lift_value b]. *)
      subst p.
      destruct scrutinee as [ | b0 | n | s ]; simpl; try reflexivity.
      * destruct (Bool.bool_dec b0 b0) as [_ | Hne]; [reflexivity | exfalso; apply Hne; reflexivity].
      * destruct (Z.eq_dec n n) as [_ | Hne]; [reflexivity | exfalso; apply Hne; reflexivity].
      * destruct (String.string_dec s s) as [_ | Hne]; [reflexivity | exfalso; apply Hne; reflexivity].
    + (* Patterns differ: both sides recurse. *)
      destruct p as [ | bp | np | sp ], scrutinee as [ | bs | ns | ss ];
        simpl; try exact IH; try (exfalso; apply Hneq; reflexivity).
      * destruct (Bool.bool_dec bp bs) as [Heq | _].
        { subst bp. exfalso. apply Hneq. reflexivity. }
        exact IH.
      * destruct (Z.eq_dec np ns) as [Heq | _].
        { subst np. exfalso. apply Hneq. reflexivity. }
        exact IH.
      * destruct (String.string_dec sp ss) as [Heq | _].
        { subst sp. exfalso. apply Hneq. reflexivity. }
        exact IH.
Qed.

(** Verdict preservation for the match case, restricted to
    scalar-constant scrutinees, nullary-constructor patterns
    equated by scalar equality, and scalar-constant branch
    bodies. *)

Theorem verdict_preservation_match :
  forall (scrutinee : LexValue)
         (branches : list (LexValue * LexValue))
         (vv : LexValue),
    match_lex_verdict (MLT_Match scrutinee branches) vv <->
    match_op_verdict  (match_compile (MLT_Match scrutinee branches)) vv.
Proof.
  intros scrutinee branches vv. split.
  - (* Forward. *)
    intros [t' Hstep].
    inversion Hstep; subst.
    simpl.
    exists (MOE_Choose (lift_value scrutinee)
                       (map (fun (pb : LexValue * LexValue) =>
                               let (p, b) := pb in
                               (lift_value p, lift_value b)) branches)).
    apply MOpStepChoose.
    rewrite op_match_find_lifts.
    apply lift_value_emits.
  - (* Backward. *)
    intros [e' Hstep].
    simpl in Hstep.
    inversion Hstep; subst.
    match goal with
    | [ H : op_step _ (LEmit vv) _ |- _ ] =>
        rewrite op_match_find_lifts in H;
        apply lift_value_emits_unique in H;
        subst vv
    end.
    exists (MLT_Match scrutinee branches).
    apply MLexStepMatch.
Qed.

(* ------------------------------------------------------------------ *)
(**  15.  Defeasible case.                                           *)
(* ------------------------------------------------------------------ *)

(** The §6.2 defeasible rule:

      [[Defeasible { base, exceptions }]]  =
        let sorted = exceptions ordered by (priority DESC, source-position ASC) in
        choose {
          when [[g_1]] -> [[b_1]];
          ...;
          when [[g_n]] -> [[b_n]];
          else -> [[base]]
        }

    Scope. The admissible fragment is restricted here to:

      - a scalar-constant base body;
      - a pre-sorted exception list [(priority, source_pos, guard, body)]
        carrying boolean guards and scalar-constant bodies;
      - fixed priority / source-position witnesses on each exception.

    The priority ordering is realized by insisting the caller supply
    a list already sorted by (priority DESC, source_position ASC),
    matching the sort performed by the Rust reference at the head of
    [compile_defeasible] in [crates/op-lex-compiler/src/
    case_defeasible.rs]. The two metadata fields are carried through
    the Coq inductive unchanged so the mechanization can compare
    exception positions when the list-induction proof traverses the
    exceptions in supplied order.

    Mechanization strategy. A new [DefLexTerm] / [DefOpExpr] layer
    over the scalar-constant fragment. The base body is a single
    [LexValue]; each exception is a 4-tuple [(priority, source_pos,
    guard_bool, body_value)]. [def_compile] lifts the base and every
    exception body, and lifts each boolean guard to [OE_Bool].
    Reduction on both sides walks the exception list in supplied
    order: the first exception whose guard is [true] fires, emitting
    its body; if no guard fires, both sides emit the base. Verdict
    preservation follows by list induction on the exceptions: at
    each step, the guard is [true] or [false]; either side agrees
    pointwise through the [lift_value] / [OE_Bool] image. *)

(** Concrete Lex head for the defeasible fragment. The base is a
    scalar value; each exception is a 4-tuple carrying its priority,
    source-position, boolean guard evaluation, and scalar body. The
    list is consumed in supplied order — the caller is expected to
    have sorted by (priority DESC, source_position ASC). *)

Inductive DefLexTerm : Type :=
  | DLT_Def : LexValue -> list (nat * nat * bool * LexValue) -> DefLexTerm.

(** Concrete Op form for the defeasible fragment. The compiled image
    carries the lifted base and the pointwise-lifted exception list;
    each exception's guard becomes an [OE_Bool] literal and each
    body becomes a lifted scalar. The priority / source-position
    metadata is not carried into Op (the Rust reference collapses
    these into the nested [Match] arm order at compile time). *)

Inductive DefOpExpr : Type :=
  | DOE_Choose : OpExpr -> list (OpExpr * OpExpr) -> DefOpExpr.

(** Lex-side evaluator. Walks the exception list in supplied order;
    returns the body of the first exception whose guard is [true];
    falls through to the base when the list is exhausted. *)

Fixpoint def_eval (base : LexValue)
                  (exceptions : list (nat * nat * bool * LexValue))
                  : LexValue :=
  match exceptions with
  | nil => base
  | (_, _, g, b) :: rest =>
      if g then b else def_eval base rest
  end.

(** Op-side evaluator. Walks the compiled exception list in supplied
    order; returns the body of the first exception whose lifted
    guard is [OE_Bool true]; falls through to the lifted base when
    the list is exhausted. Any non-boolean guard shape forces
    fall-through (the scalar-boolean-guard scope is enforced by
    [def_compile]). *)

Fixpoint def_op_find (base : OpExpr)
                     (exceptions : list (OpExpr * OpExpr))
                     : OpExpr :=
  match exceptions with
  | nil => base
  | (g, b) :: rest =>
      match g with
      | OE_Bool true  => b
      | OE_Bool false => def_op_find base rest
      | _             => def_op_find base rest
      end
  end.

(** Lex reduction for the defeasible fragment. A [DLT_Def base exs]
    emits [def_eval base exs] in one observable step. *)

Inductive def_lex_step : DefLexTerm -> Label -> DefLexTerm -> Prop :=
  | DLexStepDef :
      forall base exceptions,
        def_lex_step
          (DLT_Def base exceptions)
          (LEmit (def_eval base exceptions))
          (DLT_Def base exceptions).

(** Op reduction for the defeasible fragment. The outer [DOE_Choose]
    emits [v] when the body selected by [def_op_find] emits [v]
    under the scalar [op_step]. *)

Inductive def_op_step : DefOpExpr -> Label -> DefOpExpr -> Prop :=
  | DOpStepChoose :
      forall base exceptions v,
        op_step (def_op_find base exceptions) (LEmit v)
                (def_op_find base exceptions) ->
        def_op_step
          (DOE_Choose base exceptions)
          (LEmit v)
          (DOE_Choose base exceptions).

(** Compilation, defeasible fragment. Mirrors the Rust reference in
    [crates/op-lex-compiler/src/case_defeasible.rs] for the
    scalar-constant-base, boolean-guard, scalar-constant-body
    restriction: the base is lifted, each exception's guard is
    lifted to [OE_Bool] and its body to the lifted scalar. The sort
    performed by the Rust reference is assumed to have been carried
    out by the caller; the list is consumed in supplied order. *)

Definition def_compile (t : DefLexTerm) : DefOpExpr :=
  match t with
  | DLT_Def base exceptions =>
      DOE_Choose
        (lift_value base)
        (map (fun (e : nat * nat * bool * LexValue) =>
                let '(_, _, g, b) := e in
                (OE_Bool g, lift_value b)) exceptions)
  end.

Definition def_lex_verdict (t : DefLexTerm) (v : LexValue) : Prop :=
  exists t', def_lex_step t (LEmit v) t'.

Definition def_op_verdict (e : DefOpExpr) (v : LexValue) : Prop :=
  exists e', def_op_step e (LEmit v) e'.

(** Helper. The Op-side selector, parameterized by the lifted base
    and the pointwise-lifted exception list, selects the lifted
    image of the Lex-side evaluator's result. Proof by list
    induction on the exceptions; each step discriminates on the
    boolean guard and closes on either branch. *)

Lemma def_op_find_lifts :
  forall base exceptions,
    def_op_find (lift_value base)
                (map (fun (e : nat * nat * bool * LexValue) =>
                        let '(_, _, g, b) := e in
                        (OE_Bool g, lift_value b)) exceptions)
    = lift_value (def_eval base exceptions).
Proof.
  induction exceptions as [ | [[[p s] g] b] rest IH].
  - simpl. reflexivity.
  - simpl. destruct g.
    + (* Guard fires: Op selects [lift_value b]; Lex selects [b]. *)
      reflexivity.
    + (* Guard does not fire: both sides recurse. *)
      exact IH.
Qed.

(** Verdict preservation for the defeasible case, restricted to a
    scalar-constant base, boolean guards, and scalar-constant
    exception bodies. *)

Theorem verdict_preservation_defeasible :
  forall (base : LexValue)
         (exceptions : list (nat * nat * bool * LexValue))
         (vv : LexValue),
    def_lex_verdict (DLT_Def base exceptions) vv <->
    def_op_verdict  (def_compile (DLT_Def base exceptions)) vv.
Proof.
  intros base exceptions vv. split.
  - (* Forward. *)
    intros [t' Hstep].
    inversion Hstep; subst.
    simpl.
    exists (DOE_Choose (lift_value base)
                       (map (fun (e : nat * nat * bool * LexValue) =>
                               let '(_, _, g, b) := e in
                               (OE_Bool g, lift_value b)) exceptions)).
    apply DOpStepChoose.
    rewrite def_op_find_lifts.
    apply lift_value_emits.
  - (* Backward. *)
    intros [e' Hstep].
    simpl in Hstep.
    inversion Hstep; subst.
    match goal with
    | [ H : op_step _ (LEmit vv) _ |- _ ] =>
        rewrite def_op_find_lifts in H;
        apply lift_value_emits_unique in H;
        subst vv
    end.
    exists (DLT_Def base exceptions).
    apply DLexStepDef.
Qed.

(* ------------------------------------------------------------------ *)
(**  16.  Hole-fill case.                                            *)
(* ------------------------------------------------------------------ *)

(** The §6.2 / §6.3 hole-fill rule:

      [[HoleFill { hole_id, value, witness }]] =
        Seq(attestation.append(witness), [[value]])

    The attestation append is [tau]-labelled: it extends the Op
    trace but does not itself introduce a verdict. The observable
    verdict is therefore the verdict of the filler value, reached
    after a finite silent prefix. The proof below mirrors the Rust
    [case_fill.rs] shape exactly and closes by weak simulation up to
    [tau]. *)

Record FillWitness : Type := {
  fill_authority : string;
  fill_digest    : string;
  fill_timestamp : string
}.

Inductive FillLexTerm : Type :=
  | FLT_Fill : string -> LexValue -> FillWitness -> FillLexTerm.

Inductive FillOpExpr : Type :=
  | FOE_Lit     : LexValue -> FillOpExpr
  | FOE_AttCall : FillWitness -> FillOpExpr
  | FOE_Seq     : FillOpExpr -> FillOpExpr -> FillOpExpr.

(** Lex reduction. A filled hole emits the filler verdict directly.
    The witness is recorded on the Op side only. *)

Inductive fill_lex_step : FillLexTerm -> Label -> FillLexTerm -> Prop :=
  | FLexStepFill :
      forall hole_id v w,
        fill_lex_step (FLT_Fill hole_id v w) (LEmit v) (FLT_Fill hole_id v w).

(** Op reduction. [FOE_Lit v] emits [v]. A sequenced attestation call
    contributes one silent step, then yields control to the value
    expression. *)

Inductive fill_op_step : FillOpExpr -> Label -> FillOpExpr -> Prop :=
  | FOpStepLit :
      forall v,
        fill_op_step (FOE_Lit v) (LEmit v) (FOE_Lit v)
  | FOpStepSeqAtt :
      forall w e,
        fill_op_step (FOE_Seq (FOE_AttCall w) e) LTau e.

Definition fill_compile (t : FillLexTerm) : FillOpExpr :=
  match t with
  | FLT_Fill _ v w => FOE_Seq (FOE_AttCall w) (FOE_Lit v)
  end.

Definition fill_lex_verdict (t : FillLexTerm) (v : LexValue) : Prop :=
  exists t', fill_lex_step t (LEmit v) t'.

Inductive fill_op_tau_star : FillOpExpr -> FillOpExpr -> Prop :=
  | FOpTauRefl :
      forall e,
        fill_op_tau_star e e
  | FOpTauStep :
      forall e1 e2 e3,
        fill_op_step e1 LTau e2 ->
        fill_op_tau_star e2 e3 ->
        fill_op_tau_star e1 e3.

Definition fill_op_weak_verdict (e : FillOpExpr) (v : LexValue) : Prop :=
  exists e1 e2,
    fill_op_tau_star e e1 /\
    fill_op_step e1 (LEmit v) e2.

Lemma fill_lex_emit_unique :
  forall hole_id v w vv t',
    fill_lex_step (FLT_Fill hole_id v w) (LEmit vv) t' ->
    vv = v.
Proof.
  intros hole_id v w vv t' Hstep.
  inversion Hstep; reflexivity.
Qed.

Lemma fill_lit_emit_unique :
  forall v vv e',
    fill_op_step (FOE_Lit v) (LEmit vv) e' ->
    vv = v.
Proof.
  intros v vv e' Hstep.
  inversion Hstep; reflexivity.
Qed.

(** Weak simulation up to [tau] on the Op side. Every Lex emission
    must be matchable by a finite [tau]-prefix followed by the same
    observable verdict on the Op side; observable and silent Op steps
    must be reflectable back into the Lex term. *)

CoInductive weak_sim : FillLexTerm -> FillOpExpr -> Prop :=
  | wsim_step :
      forall t e,
        (forall vv t',
            fill_lex_step t (LEmit vv) t' ->
            exists e1 e2,
              fill_op_tau_star e e1 /\
              fill_op_step e1 (LEmit vv) e2 /\
              weak_sim t' e2) ->
        (forall vv e',
            fill_op_step e (LEmit vv) e' ->
            exists t',
              fill_lex_step t (LEmit vv) t' /\
              weak_sim t' e') ->
        (forall e',
            fill_op_step e LTau e' ->
            weak_sim t e') ->
        weak_sim t e.

(** Once the [tau]-labelled attestation append has fired, the Op side
    is just the stable literal state. This cofixpoint is kept separate
    so the recursive calls remain visibly guarded by [wsim_step]. *)

CoFixpoint fill_post_stable
  (hole_id : string) (v : LexValue) (w : FillWitness)
  : weak_sim (FLT_Fill hole_id v w) (FOE_Lit v).
Proof.
  refine (wsim_step
            (t := FLT_Fill hole_id v w)
            (e := FOE_Lit v)
            _
            _
            _).
  - intros vv t' Hstep.
    inversion Hstep; subst t'. subst vv.
    exists (FOE_Lit v), (FOE_Lit v).
    split.
    + constructor.
    + split.
      * constructor.
      * exact (fill_post_stable hole_id v w).
  - intros vv e' Hstep.
    inversion Hstep; subst e'. subst vv.
    exists (FLT_Fill hole_id v w).
    split.
    + constructor.
    + exact (fill_post_stable hole_id v w).
  - intros e' Hstep.
    inversion Hstep.
Qed.

(** The compiled fill term simulates the source fill term after one
    silent attestation step, then hands off to the stable literal
    simulation above. *)

Lemma fill_bisim :
  forall hole_id v w,
    weak_sim (FLT_Fill hole_id v w)
             (fill_compile (FLT_Fill hole_id v w)).
Proof.
  intros hole_id v w.
  refine (wsim_step
            (t := FLT_Fill hole_id v w)
            (e := fill_compile (FLT_Fill hole_id v w))
            _
            _
            _).
  - intros vv t' Hstep.
    inversion Hstep; subst t'. subst vv.
    exists (FOE_Lit v), (FOE_Lit v).
    split.
    + simpl. econstructor.
      * constructor.
      * constructor.
    + split.
      * constructor.
      * exact (fill_post_stable hole_id v w).
  - intros vv e' Hstep.
    inversion Hstep.
  - intros e' Hstep.
    inversion Hstep; subst.
    apply fill_post_stable.
Qed.

Lemma weak_sim_lex_to_op :
  forall t e vv,
    weak_sim t e ->
    fill_lex_verdict t vv ->
    fill_op_weak_verdict e vv.
Proof.
  intros t e vv Hsim [t' Hstep].
  inversion Hsim as [t0 e0 Hlex Hop _]; subst.
  destruct (Hlex vv t' Hstep) as [e1 [e2 [Htau [Hemit _]]]].
  exists e1, e2.
  split; assumption.
Qed.

Lemma weak_sim_tau_to_lex :
  forall t e e_mid vv e',
    weak_sim t e ->
    fill_op_tau_star e e_mid ->
    fill_op_step e_mid (LEmit vv) e' ->
    fill_lex_verdict t vv.
Proof.
  intros t e e_mid vv e' Hsim Htau.
  revert t Hsim vv e'.
  induction Htau as [e0 | e0 e1 e2 Hstep Htau IH];
    intros t Hsim vv e' Hemit.
  - inversion Hsim as [t0 e0' _ Hop _]; subst.
    destruct (Hop vv e' Hemit) as [t' [Hlex _]].
    exists t'. exact Hlex.
  - inversion Hsim as [t0 e0' _ _ Htau_match]; subst.
    eapply IH.
    + apply Htau_match with (e' := e1). exact Hstep.
    + exact Hemit.
Qed.

Theorem verdict_preservation_fill :
  forall (hole_id : string)
         (filler : LexValue)
         (witness : FillWitness)
         (vv : LexValue),
    fill_lex_verdict (FLT_Fill hole_id filler witness) vv <->
    fill_op_weak_verdict
      (fill_compile (FLT_Fill hole_id filler witness)) vv.
Proof.
  intros hole_id filler witness vv.
  split.
  - intros Hlex.
    eapply weak_sim_lex_to_op.
    + apply fill_bisim.
    + exact Hlex.
  - intros [e1 [e2 [Htau Hemit]]].
    eapply weak_sim_tau_to_lex.
    + apply fill_bisim.
    + exact Htau.
    + exact Hemit.
Qed.

(* ------------------------------------------------------------------ *)
(**  13.  End-to-end sanity examples.                                *)
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
