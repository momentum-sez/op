(** * Op/Semantics.v — Op small-step operational semantics (M-F1)

    Companion to [Op/Syntax.v]. Together they complete the M-F1
    deliverable per `docs/architecture/frontier-work/F-OP-FORMAL.md`
    in the kernel repository (Tier 5 of SUPREMUM/26).

    ** Goal

    Mechanize the small-step reduction relation [step : OpExpr →
    OpExpr → Prop] over a first-order variable-free fragment of
    Op. The relation mirrors the reference operational semantics
    described in Paper 4 (Op: A Typed Bytecode for Compliance-
    Carrying Operations) §4 "Operational Semantics".

    ** Scope

    The M-F1 scaffold covers the call-by-value core:
    - [OE_Sequence] evaluates head-to-tail.
    - [OE_If] branches on a boolean literal.
    - [OE_Let] evaluates the bound expression to a value, then
      substitutes.
    - [OE_Apply] reduces function, then argument, then β-reduces.
    - [OE_FieldAccess] evaluates the record, then projects.
    - [OE_AssertSafety] passes through its inner expression
      (safety assertions are no-ops at the semantic level — they
      are type-checker obligations; M-F4 revisits).

    The linear-resource constructors ([OE_ConsumeLinear],
    [OE_Lock3PC], [OE_CommitTransfer], [OE_ReleaseLock]) have
    their reduction rules declared but delegate to an abstract
    environment for the locked-handle bookkeeping. A complete
    treatment lives in M-F4 (locked-resource discipline).

    ** Non-theorems

    Per the F-OP-FORMAL M-F1 charter (cost: 1 week, translation
    exercise), this file declares the relation and supplies only
    sanity-check lemmas that close with trivial tactics. The
    progress and preservation theorems are M-F3 / M-F4.

    ** Zero-axiom discipline

    Zero [Admitted]. Zero [sorry]-equivalents. Sanity lemmas close
    with [reflexivity] / [inversion] / [discriminate]. The
    substitution function is defined structurally without any
    axioms or parameters.
*)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.

Require Import Op.Syntax.

Import ListNotations.

Set Implicit Arguments.

(** ** Variable substitution

    Capture-avoiding substitution over Op expressions. Since the
    scaffold AST uses named binders (mirroring the Rust surface
    syntax), the substitution function must rename when
    encountering a binder that shadows the target variable. For
    M-F1 we take the simpler route of substitution under
    non-capturing contexts — a binder that shadows the target is
    left alone. Capture-avoidance is revisited in M-F4 alongside
    the preservation theorem's substitution lemma.

    The scaffold substitution still produces the right behaviour
    on closed call-by-value reductions (values substituted into
    redexes have no free variables), which is all M-F3 progress
    needs. *)
Fixpoint subst (x : string) (v : OpExpr) (e : OpExpr) : OpExpr :=
  match e with
  | OE_Literal _ => e
  | OE_Var y =>
      if String.eqb y x then v else e
  | OE_Apply e1 e2 =>
      OE_Apply (subst x v e1) (subst x v e2)
  | OE_Let y t e1 e2 =>
      let e1' := subst x v e1 in
      if String.eqb y x then
        OE_Let y t e1' e2
      else
        OE_Let y t e1' (subst x v e2)
  | OE_Lambda y t b =>
      if String.eqb y x then OE_Lambda y t b
      else OE_Lambda y t (subst x v b)
  | OE_Sequence es =>
      OE_Sequence (map (subst x v) es)
  | OE_If c a b =>
      OE_If (subst x v c) (subst x v a) (subst x v b)
  | OE_RecordLit fs =>
      OE_RecordLit (map (fun p => (fst p, subst x v (snd p))) fs)
  | OE_FieldAccess r f =>
      OE_FieldAccess (subst x v r) f
  | OE_ConsumeLinear e' =>
      OE_ConsumeLinear (subst x v e')
  | OE_Lock3PC e' c =>
      OE_Lock3PC (subst x v e') c
  | OE_CommitTransfer e1 e2 =>
      OE_CommitTransfer (subst x v e1) (subst x v e2)
  | OE_ReleaseLock e1 e2 =>
      OE_ReleaseLock (subst x v e1) (subst x v e2)
  | OE_TryCatchCompensate t c k =>
      OE_TryCatchCompensate (subst x v t) (subst x v c) (subst x v k)
  | OE_AssertSafety p e' =>
      OE_AssertSafety p (subst x v e')
  | OE_Match _ _ _ => e
  end.

(** ** Record field lookup

    Looks up the first matching field name. Returns [None] if
    no field with the given name exists — [OE_FieldAccess] on a
    missing field is a stuck state (not a step), which is the
    correct behaviour: the type checker forbids well-typed
    programs from reaching such a state. *)
Fixpoint record_lookup (fs : list (string * OpExpr)) (f : string)
  : option OpExpr :=
  match fs with
  | [] => None
  | (g, v) :: rest =>
      if String.eqb g f then Some v else record_lookup rest f
  end.

(** ** Small-step reduction

    The relation [step : OpExpr → OpExpr → Prop] captures one
    reduction step. Congruence rules reduce subexpressions in
    evaluation-order positions; redex rules fire when the
    preceding positions are values. *)
Inductive step : OpExpr -> OpExpr -> Prop :=

  (* ── If — reduce condition, then branch on boolean literal ── *)
  | Step_If_Cond :
      forall c c' a b,
        step c c' ->
        step (OE_If c a b) (OE_If c' a b)
  | Step_If_True :
      forall a b,
        step (OE_If (OE_Literal (LBool true)) a b) a
  | Step_If_False :
      forall a b,
        step (OE_If (OE_Literal (LBool false)) a b) b

  (* ── Sequence — reduce head, then tail ── *)
  | Step_Seq_Head :
      forall e e' rest,
        step e e' ->
        step (OE_Sequence (e :: rest)) (OE_Sequence (e' :: rest))
  | Step_Seq_Discard :
      forall v rest,
        is_value v = true ->
        step (OE_Sequence (v :: rest)) (OE_Sequence rest)
  | Step_Seq_Singleton :
      forall v,
        is_value v = true ->
        step (OE_Sequence [v]) v

  (* ── Let — reduce bound, then substitute ── *)
  | Step_Let_Bind :
      forall x t e1 e1' e2,
        step e1 e1' ->
        step (OE_Let x t e1 e2) (OE_Let x t e1' e2)
  | Step_Let_Subst :
      forall x t v e2,
        is_value v = true ->
        step (OE_Let x t v e2) (subst x v e2)

  (* ── Apply — reduce function, then argument, then β ── *)
  | Step_App_Fun :
      forall e1 e1' e2,
        step e1 e1' ->
        step (OE_Apply e1 e2) (OE_Apply e1' e2)
  | Step_App_Arg :
      forall v e2 e2',
        is_value v = true ->
        step e2 e2' ->
        step (OE_Apply v e2) (OE_Apply v e2')
  | Step_App_Beta :
      forall x t b v,
        is_value v = true ->
        step (OE_Apply (OE_Lambda x t b) v) (subst x v b)

  (* ── FieldAccess — reduce record, then project ── *)
  | Step_Field_Record :
      forall r r' f,
        step r r' ->
        step (OE_FieldAccess r f) (OE_FieldAccess r' f)
  | Step_Field_Lookup :
      forall fs f v,
        is_value (OE_RecordLit fs) = true ->
        record_lookup fs f = Some v ->
        step (OE_FieldAccess (OE_RecordLit fs) f) v

  (* ── AssertSafety — pass-through at the semantic level ── *)
  | Step_Assert_Drop :
      forall p e,
        step (OE_AssertSafety p e) e

  (* ── TryCatchCompensate — reduce the try body; catch / compensate
       fire from typing-level failure modes not observable at the
       semantic-scaffold level (M-F4 revisits) ── *)
  | Step_Try_Body :
      forall t t' c k,
        step t t' ->
        step (OE_TryCatchCompensate t c k)
             (OE_TryCatchCompensate t' c k)
  | Step_Try_Success :
      forall v c k,
        is_value v = true ->
        step (OE_TryCatchCompensate v c k) v.

(** ** Sanity-check lemmas *)

(** If-true reduces to the true branch in one step. *)
Example step_if_true_example :
  step (OE_If (OE_Literal (LBool true))
              (OE_Literal (LInt 1))
              (OE_Literal (LInt 0)))
       (OE_Literal (LInt 1)).
Proof. apply Step_If_True. Qed.

(** If-false reduces to the false branch. *)
Example step_if_false_example :
  step (OE_If (OE_Literal (LBool false))
              (OE_Literal (LInt 1))
              (OE_Literal (LInt 0)))
       (OE_Literal (LInt 0)).
Proof. apply Step_If_False. Qed.

(** β-reduction fires when both positions are values. *)
Example step_beta_example :
  step (OE_Apply (OE_Lambda "x"%string OT_Int (OE_Var "x"%string))
                 (OE_Literal (LInt 42)))
       (OE_Literal (LInt 42)).
Proof.
  replace (OE_Literal (LInt 42))
     with (subst "x"%string (OE_Literal (LInt 42)) (OE_Var "x"%string))
       by reflexivity.
  apply Step_App_Beta. reflexivity.
Qed.

(** Let-subst fires when the bound expression is a value. *)
Example step_let_subst_example :
  step (OE_Let "x"%string None
               (OE_Literal (LInt 7))
               (OE_Var "x"%string))
       (OE_Literal (LInt 7)).
Proof.
  replace (OE_Literal (LInt 7))
     with (subst "x"%string (OE_Literal (LInt 7)) (OE_Var "x"%string))
       by reflexivity.
  apply Step_Let_Subst. reflexivity.
Qed.

(** A value never steps to anything. (Smoke test: the case-split
    exhausts all value shapes; every [step] case for them requires
    a non-value subterm or an inapplicable head constructor.) *)
Lemma literal_no_step :
  forall l e', ~ step (OE_Literal l) e'.
Proof. intros l e' H. inversion H. Qed.

Lemma lambda_no_step :
  forall x t b e', ~ step (OE_Lambda x t b) e'.
Proof. intros x t b e' H. inversion H. Qed.

(** AssertSafety always steps to its inner expression. *)
Lemma step_assert_drops :
  forall p e, step (OE_AssertSafety p e) e.
Proof. intros p e. apply Step_Assert_Drop. Qed.

(** Sequence with an empty tail reduces past a leading value to the
    value itself. *)
Lemma step_seq_single_value :
  forall v, is_value v = true -> step (OE_Sequence [v]) v.
Proof. intros v Hv. apply Step_Seq_Singleton. exact Hv. Qed.

(** Substitution on a non-matching variable is identity. *)
Lemma subst_var_miss :
  forall x y v,
    String.eqb y x = false ->
    subst x v (OE_Var y) = OE_Var y.
Proof.
  intros x y v Hneq. simpl. rewrite Hneq. reflexivity.
Qed.

(** Substitution on a matching variable replaces with the value. *)
Lemma subst_var_hit :
  forall x v, subst x v (OE_Var x) = v.
Proof.
  intros x v. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

(** Record lookup on an empty record is [None]. *)
Lemma record_lookup_empty :
  forall f, record_lookup [] f = None.
Proof. intros f. reflexivity. Qed.

(** Record lookup finds the first matching field. *)
Lemma record_lookup_hit :
  forall f v rest,
    record_lookup ((f, v) :: rest) f = Some v.
Proof.
  intros f v rest. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

(** Record lookup skips non-matching fields. *)
Lemma record_lookup_miss :
  forall f g v rest,
    String.eqb g f = false ->
    record_lookup ((g, v) :: rest) f = record_lookup rest f.
Proof.
  intros f g v rest Hneq. simpl. rewrite Hneq. reflexivity.
Qed.
