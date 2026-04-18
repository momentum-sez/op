(** * CompilationSoundness.v

    Mechanization of verdict preservation for the compilation function
    [[.]] : Lex -> Op.

    Two cases are mechanized and closed with [Qed.]:

      1. Scalar constant case (§6.2).
      2. Sanctions-dominance case (§6.2 / §6.3).

    Scope.

      - Lex AST (admissible fragment, constant head constructor,
        scalar payloads; plus sanctions-dominance head for case 2)
      - Op AST (expression fragment sufficient for lifted scalar
        constants; plus host-call form for case 2)
      - value-lifting function [lift_value : LexValue -> OpExpr]
      - compilation function [compile : LexTerm -> OpExpr]
      - small-step operational semantics for Lex and Op with a trace
        alphabet distinguishing silent [tau] transitions from
        observable verdict emissions
      - verdict-extraction predicates on Lex terms and Op expressions
      - the verdict-preservation theorems for the scalar constant and
        sanctions-dominance cases, proved in both directions

    The remaining shapes of the constant case (records, lists,
    variants) and the remaining four compilation cases (variable,
    match, defeasible, hole_fill) are registered in the [Obligations]
    section as [Admitted.] theorems carrying honest proof-obligation
    statements that a follow-on mechanization will discharge. *)

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
(**  10.  Proof obligations.                                          *)
(* ------------------------------------------------------------------ *)

(** The §6.2 compilation function comprises six cases. The scalar
    shape of the constant case and the sanctions-dominance case are
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
      definitions (records, lists, variants; variable references;
      match expressions; defeasible rules; filled holes) taken from
      the Rust reference. *)

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
(**  11.  End-to-end sanity examples.                                *)
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
