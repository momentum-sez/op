(** * CompilationSoundness.v

    Mechanization of verdict preservation for the compilation function
    [[.]] : Lex -> Op.

    Four cases are mechanized and closed with [Qed.]:

      1. Scalar constant case (§6.2).
      2. Sanctions-dominance case (§6.2 / §6.3).
      3. Variable case (§6.2), against a shared prelude parameter.
      4. Constant case — record shape (§6.2), restricted to records
         whose field values are scalars.

    Scope.

      - Lex AST (admissible fragment, constant head constructor,
        scalar payloads; plus sanctions-dominance head for case 2;
        plus constant/variable heads for case 3; plus record-constant
        head for case 4)
      - Op AST (expression fragment sufficient for lifted scalar
        constants; plus host-call form for case 2; plus
        literal/variable forms for case 3; plus record form for
        case 4)
      - value-lifting function [lift_value : LexValue -> OpExpr]
      - compilation functions [compile : LexTerm -> OpExpr],
        [sanct_compile], [var_compile], [rec_compile]
      - small-step operational semantics for Lex and Op with a trace
        alphabet distinguishing silent [tau] transitions from
        observable verdict emissions; the record case uses a field
        list as its emission payload
      - verdict-extraction predicates on Lex terms and Op expressions
      - the verdict-preservation theorems for the four mechanized
        cases, proved in both directions

    The remaining shapes of the constant case (lists, variants) and
    the remaining three compilation cases (match, defeasible,
    hole_fill) are registered in the [Obligations] section as
    [Admitted.] theorems carrying honest proof-obligation statements
    that a follow-on mechanization will discharge. *)

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
    the record shape is mechanized in §11 below; the list and
    variant shapes are registered in the obligations section. *)

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

(** Host primitive. Axiomatized as a deterministic function from
    principals to the two-element verdict set. The range axiom is
    load-bearing: the case-split on [host_sanctions v_p] is the
    crux of the proof. *)

Parameter host_sanctions : LexValue -> LexValue.

Axiom host_sanctions_range :
  forall p,
    host_sanctions p = LV_Str "Compliant" \/
    host_sanctions p = LV_Str "SanctionsBlocked".

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

(** Sanity. The verdict is always one of the two host outputs. *)

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
(**  12.  Proof obligations.                                          *)
(* ------------------------------------------------------------------ *)

(** The §6.2 compilation function comprises six cases. The scalar
    shape of the constant case, the sanctions-dominance case, the
    variable case, and the record shape of the constant case are
    closed above. The remaining obligations are registered below as
    [Admitted.] theorems carrying the signature of the target result
    and a proof-structure comment.

    The shapes introduced here as parameters mirror the Rust AST
    extensions in [crates/op-lex-compiler/src/ast.rs]. A follow-on
    file replaces each [Parameter] with the corresponding
    [Inductive] definition and discharges the [Admitted.]
    statements. *)

Section Obligations.

  (** Parameters carried across this obligations section. Each
      follow-on refinement replaces these with concrete syntactic
      definitions (lists, variants; match expressions; defeasible
      rules; filled holes) taken from the Rust reference. *)

  Parameter ExtLexTerm     : Type.
  Parameter ExtOpExpr      : Type.
  Parameter ExtCompile     : ExtLexTerm -> ExtOpExpr.
  Parameter ExtLexVerdict  : ExtLexTerm -> LexValue -> Prop.
  Parameter ExtOpVerdict   : ExtOpExpr  -> LexValue -> Prop.

  Parameter ELV_List    : list LexValue -> LexValue.
  Parameter ELV_Variant : string -> LexValue -> LexValue.
  Parameter ELT_Const   : LexValue -> ExtLexTerm.

  Parameter ELT_Match      : ExtLexTerm -> list (string * string * ExtLexTerm) -> ExtLexTerm.
  Parameter ELT_Defeasible : string -> ExtLexTerm -> list (ExtLexTerm * ExtLexTerm * nat * nat) -> ExtLexTerm.
  Parameter ELT_HoleFill   : string -> ExtLexTerm -> ExtLexTerm.

  (** ** Constant case — list / variant shapes.

      Goal. Verdict preservation extends to list and variant
      constructors.

      Proof strategy. Structural induction on the [LexValue]
      constructor, with a nested induction on the list of elements
      (list case). The inductive step uses the scalar base cases
      proved above. *)

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
