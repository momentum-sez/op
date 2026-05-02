Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Equality.

Inductive ty : Type :=
  | T_Nat : ty
  | T_Arrow : ty -> ty -> ty.

Inductive expr : Type :=
  | E_Const : nat -> expr
  | E_Var : nat -> expr
  | E_Let : nat -> expr -> expr -> expr
  | E_Lam : nat -> ty -> expr -> expr
  | E_App : expr -> expr -> expr.

Definition context := list (nat * ty).

Fixpoint lookup (G : context) (x : nat) : option ty :=
  match G with
  | [] => None
  | (y, T) :: G' => if Nat.eq_dec x y then Some T else lookup G' x
  end.

Inductive value : expr -> Prop :=
  | V_Const : forall n, value (E_Const n)
  | V_Lam : forall x T e, value (E_Lam x T e).

Inductive has_type : context -> expr -> ty -> Prop :=
  | T_Const :
      forall G n,
        has_type G (E_Const n) T_Nat
  | T_Var :
      forall G x T,
        lookup G x = Some T ->
        has_type G (E_Var x) T
  | T_Let :
      forall G z e1 e2 U T,
        has_type G e1 U ->
        has_type ((z, U) :: G) e2 T ->
        has_type G (E_Let z e1 e2) T
  | T_Lam :
      forall G z U e T,
        has_type ((z, U) :: G) e T ->
        has_type G (E_Lam z U e) (T_Arrow U T)
  | T_App :
      forall G e1 e2 U T,
        has_type G e1 (T_Arrow U T) ->
        has_type G e2 U ->
        has_type G (E_App e1 e2) T.

Fixpoint closed_at (bound : list nat) (e : expr) : Prop :=
  match e with
  | E_Const _ => True
  | E_Var x => In x bound
  | E_Let z e1 e2 => closed_at bound e1 /\ closed_at (z :: bound) e2
  | E_Lam z _ e1 => closed_at (z :: bound) e1
  | E_App e1 e2 => closed_at bound e1 /\ closed_at bound e2
  end.

Definition closed (e : expr) : Prop := closed_at [] e.

Fixpoint subst (x : nat) (v : expr) (e : expr) : expr :=
  match e with
  | E_Const n => E_Const n
  | E_Var y => if Nat.eq_dec y x then v else E_Var y
  | E_Let z e1 e2 =>
      E_Let z
        (subst x v e1)
        (if Nat.eq_dec z x then e2 else subst x v e2)
  | E_Lam z T e1 =>
      E_Lam z T
        (if Nat.eq_dec z x then e1 else subst x v e1)
  | E_App e1 e2 => E_App (subst x v e1) (subst x v e2)
  end.

Inductive step : expr -> expr -> Prop :=
  | ST_App1 :
      forall e1 e1' e2,
        step e1 e1' ->
        step (E_App e1 e2) (E_App e1' e2)
  | ST_App2 :
      forall v1 e2 e2',
        value v1 ->
        step e2 e2' ->
        step (E_App v1 e2) (E_App v1 e2')
  | ST_AppBeta :
      forall x T e v,
        value v ->
        closed v ->
        step (E_App (E_Lam x T e) v) (subst x v e)
  | ST_Let1 :
      forall x e1 e1' e2,
        step e1 e1' ->
        step (E_Let x e1 e2) (E_Let x e1' e2)
  | ST_LetBeta :
      forall x v e2,
        value v ->
        closed v ->
        step (E_Let x v e2) (subst x v e2).

Lemma lookup_eq :
  forall G x T,
    lookup ((x, T) :: G) x = Some T.
Proof.
  intros G x T.
  simpl.
  destruct (Nat.eq_dec x x) as [_ | Hneq].
  - reflexivity.
  - contradiction.
Qed.

Lemma lookup_neq :
  forall G x y T,
    x <> y ->
    lookup ((x, T) :: G) y = lookup G y.
Proof.
  intros G x y T Hneq.
  simpl.
  destruct (Nat.eq_dec y x) as [Heq | Hne].
  - exfalso. apply Hneq. symmetry. exact Heq.
  - reflexivity.
Qed.

Lemma lookup_in_dom :
  forall G x T,
    lookup G x = Some T ->
    In x (map fst G).
Proof.
  induction G as [| [y S] G IH]; intros x T Hlookup; simpl in *.
  - discriminate.
  - destruct (Nat.eq_dec x y) as [Heq | Hneq].
    + subst. left. reflexivity.
    + right. eapply IH. exact Hlookup.
Qed.

Lemma lookup_app_neq :
  forall Delta G x y U,
    x <> y ->
    lookup (Delta ++ ((x, U) :: G)) y = lookup (Delta ++ G) y.
Proof.
  induction Delta as [| [z S] Delta IH]; intros G x y U Hneq; simpl.
  - destruct (Nat.eq_dec y x) as [Heq | Hne].
    + exfalso. apply Hneq. symmetry. exact Heq.
    + reflexivity.
  - destruct (Nat.eq_dec y z) as [_ | _].
    + reflexivity.
    + apply IH. exact Hneq.
Qed.

Lemma lookup_app_eq :
  forall Delta G x U,
    ~ In x (map fst Delta) ->
    lookup (Delta ++ ((x, U) :: G)) x = Some U.
Proof.
  induction Delta as [| [z S] Delta IH]; intros G x U Hnotin; simpl in *.
  - apply lookup_eq.
  - destruct (Nat.eq_dec x z) as [Heq | Hneq].
    + subst. exfalso. apply Hnotin. simpl. left. reflexivity.
    + apply IH.
      intro Hin.
      apply Hnotin.
      simpl.
      right.
      exact Hin.
Qed.

Lemma lookup_cons_app_shadow :
  forall Delta G x U1 U2 y,
    lookup (((x, U1) :: Delta) ++ ((x, U2) :: G)) y =
    lookup (((x, U1) :: Delta) ++ G) y.
Proof.
  intros Delta G x U1 U2 y.
  destruct (Nat.eq_dec y x) as [Heq | Hneq].
  - subst. simpl. destruct (Nat.eq_dec x x) as [_ | Habs].
    + reflexivity.
    + contradiction.
  - simpl. destruct (Nat.eq_dec y x) as [Habs | _].
    + contradiction.
    + apply lookup_app_neq.
      intro Heq.
      apply Hneq.
      symmetry.
      exact Heq.
Qed.

Lemma context_invariance :
  forall G1 G2 e T,
    has_type G1 e T ->
    (forall x U, lookup G1 x = Some U -> lookup G2 x = Some U) ->
    has_type G2 e T.
Proof.
  intros G1 G2 e T Htyp.
  generalize dependent G2.
  induction Htyp; intros G2 Hagree.
  - constructor.
  - econstructor. apply Hagree. exact H.
  - econstructor.
    + apply IHHtyp1. exact Hagree.
    + apply IHHtyp2.
      intros y V Hlookup.
      destruct (Nat.eq_dec y z) as [Heq | Hneq].
      * subst. rewrite lookup_eq. rewrite lookup_eq in Hlookup. inversion Hlookup. reflexivity.
      * rewrite lookup_neq by (intro Heq; apply Hneq; symmetry; exact Heq).
        rewrite lookup_neq in Hlookup by (intro Heq; apply Hneq; symmetry; exact Heq).
        apply Hagree. exact Hlookup.
  - econstructor.
    apply IHHtyp.
    intros y V Hlookup.
    destruct (Nat.eq_dec y z) as [Heq | Hneq].
    + subst. rewrite lookup_eq. rewrite lookup_eq in Hlookup. inversion Hlookup. reflexivity.
    + rewrite lookup_neq by (intro Heq; apply Hneq; symmetry; exact Heq).
      rewrite lookup_neq in Hlookup by (intro Heq; apply Hneq; symmetry; exact Heq).
      apply Hagree. exact Hlookup.
  - econstructor.
    + apply IHHtyp1. exact Hagree.
    + apply IHHtyp2. exact Hagree.
Qed.

Lemma weaken_from_empty :
  forall G e T,
    has_type [] e T ->
    has_type G e T.
Proof.
  intros G e T Htyp.
  eapply context_invariance; eauto.
  intros x U Hlookup.
  inversion Hlookup.
Qed.

Lemma typing_implies_closed_at :
  forall G e T,
    has_type G e T ->
    closed_at (map fst G) e.
Proof.
  intros G e T Htyp.
  induction Htyp; simpl.
  - exact I.
  - apply lookup_in_dom with (T := T). exact H.
  - split; assumption.
  - exact IHHtyp.
  - split; assumption.
Qed.

Lemma restrict_context :
  forall G H e T,
    has_type G e T ->
    closed_at (map fst H) e ->
    (forall x U, In x (map fst H) -> lookup G x = Some U -> lookup H x = Some U) ->
    has_type H e T.
Proof.
  intros G H e T Htyp.
  generalize dependent H.
  induction Htyp; intros Hctx Hclosed Hagree.
  - constructor.
  - simpl in Hclosed.
    econstructor.
    eapply Hagree; eauto.
  - simpl in Hclosed.
    destruct Hclosed as [Hclosed1 Hclosed2].
    econstructor.
    + apply IHHtyp1; assumption.
    + apply IHHtyp2.
      * exact Hclosed2.
      * intros y V Hy Hlookup.
        destruct (Nat.eq_dec y z) as [Heq | Hneq].
        -- subst. rewrite lookup_eq. rewrite lookup_eq in Hlookup. inversion Hlookup. reflexivity.
        -- rewrite lookup_neq by (intro Heq; apply Hneq; symmetry; exact Heq).
           rewrite lookup_neq in Hlookup by (intro Heq; apply Hneq; symmetry; exact Heq).
           simpl in Hy.
           destruct Hy as [Hy | Hy].
           ++ subst. contradiction.
           ++ apply Hagree; assumption.
  - simpl in Hclosed.
    econstructor.
    apply IHHtyp.
    + exact Hclosed.
    + intros y V Hy Hlookup.
      destruct (Nat.eq_dec y z) as [Heq | Hneq].
      * subst. rewrite lookup_eq. rewrite lookup_eq in Hlookup. inversion Hlookup. reflexivity.
      * rewrite lookup_neq by (intro Heq; apply Hneq; symmetry; exact Heq).
        rewrite lookup_neq in Hlookup by (intro Heq; apply Hneq; symmetry; exact Heq).
        simpl in Hy.
        destruct Hy as [Hy | Hy].
        -- subst. contradiction.
        -- apply Hagree; assumption.
  - simpl in Hclosed.
    destruct Hclosed as [Hclosed1 Hclosed2].
    econstructor.
    + apply IHHtyp1; assumption.
    + apply IHHtyp2; assumption.
Qed.

Lemma closed_typed_empty :
  forall G e T,
    has_type G e T ->
    closed e ->
    has_type [] e T.
Proof.
  intros G e T Htyp Hclosed.
  eapply restrict_context with (H := []); eauto.
  intros x U HIn.
  inversion HIn.
Qed.

Lemma subst_preserves_general :
  forall Delta G x v e T U,
    has_type (Delta ++ ((x, U) :: G)) e T ->
    has_type [] v U ->
    ~ In x (map fst Delta) ->
    has_type (Delta ++ G) (subst x v e) T.
Proof.
  intros Delta G x v e T U Htyp.
  remember (Delta ++ ((x, U) :: G)) as Gamma eqn:HGamma.
  revert Delta G x U HGamma.
  induction Htyp; intros Delta G0 x0 U0 HGamma Hv Hnotin; subst; simpl.
  - constructor.
  - destruct (Nat.eq_dec x x0) as [Heq | Hneq].
    + subst.
      rewrite lookup_app_eq in H by exact Hnotin.
      inversion H. subst.
      apply weaken_from_empty. exact Hv.
    + econstructor.
      rewrite lookup_app_neq in H by (intro Heq; apply Hneq; symmetry; exact Heq).
      exact H.
  - destruct (Nat.eq_dec z x0) as [Heq | Hneq].
    + subst.
      econstructor.
      * eapply IHHtyp1; eauto.
      * eapply context_invariance.
        -- exact Htyp2.
        -- intros y V Hlookup.
           destruct (Nat.eq_dec y x0) as [Heq' | Hneq'].
           ++ subst. repeat rewrite lookup_eq in Hlookup. inversion Hlookup. subst.
              repeat rewrite lookup_eq. reflexivity.
           ++ simpl in Hlookup.
              destruct (Nat.eq_dec y x0) as [Heq'' | _] in Hlookup.
              ** contradiction.
              ** simpl.
                 destruct (Nat.eq_dec y x0) as [Heq'' | _].
                 --- contradiction.
                 --- idtac.
              rewrite lookup_app_neq in Hlookup by (intro Heq''; apply Hneq'; symmetry; exact Heq'').
              exact Hlookup.
    + econstructor.
      * eapply IHHtyp1; eauto.
      * replace (((z, U) :: Delta) ++ G0) with ((z, U) :: (Delta ++ G0)) by reflexivity.
        eapply (IHHtyp2 (((z, U) :: Delta)) G0 x0 U0).
        -- reflexivity.
        -- exact Hv.
        -- simpl.
           intro Hin.
           destruct Hin as [Hin | Hin].
           ++ inversion Hin. contradiction.
           ++ apply Hnotin. exact Hin.
  - destruct (Nat.eq_dec z x0) as [Heq | Hneq].
    + subst.
      econstructor.
      eapply context_invariance.
      * exact Htyp.
      * intros y V Hlookup.
        destruct (Nat.eq_dec y x0) as [Heq' | Hneq'].
        -- subst. repeat rewrite lookup_eq in Hlookup. inversion Hlookup. subst.
           repeat rewrite lookup_eq. reflexivity.
        -- simpl in Hlookup.
           destruct (Nat.eq_dec y x0) as [Heq'' | _] in Hlookup.
           ++ contradiction.
           ++ simpl.
              destruct (Nat.eq_dec y x0) as [Heq'' | _].
              ** contradiction.
              ** idtac.
           rewrite lookup_app_neq in Hlookup by (intro Heq''; apply Hneq'; symmetry; exact Heq'').
           exact Hlookup.
    + econstructor.
      replace (((z, U) :: Delta) ++ G0) with ((z, U) :: (Delta ++ G0)) by reflexivity.
      eapply (IHHtyp (((z, U) :: Delta)) G0 x0 U0).
      * reflexivity.
      * exact Hv.
      * simpl.
        intro Hin.
        destruct Hin as [Hin | Hin].
        -- inversion Hin. contradiction.
        -- apply Hnotin. exact Hin.
  - econstructor.
    + eapply IHHtyp1; eauto.
    + eapply IHHtyp2; eauto.
Qed.

Lemma subst_preserves :
  forall G x v e T U,
    has_type ((x, U) :: G) e T ->
    has_type [] v U ->
    has_type G (subst x v e) T.
Proof.
  intros G x v e T U Htyp Hv.
  change G with ([] ++ G).
  eapply subst_preserves_general with (Delta := []).
  - exact Htyp.
  - exact Hv.
  - simpl. tauto.
Qed.

Lemma canonical_forms_arrow :
  forall v U T,
    value v ->
    has_type [] v (T_Arrow U T) ->
    exists z e, v = E_Lam z U e.
Proof.
  intros v U T Hval Htyp.
  inversion Hval; subst.
  - inversion Htyp.
  - inversion Htyp; subst.
    match goal with
    | |- exists z e, E_Lam ?x U ?body = E_Lam z U e =>
        exists x, body; reflexivity
    end.
Qed.

Theorem op_progress :
  forall e T,
    has_type [] e T ->
    value e \/ exists e', step e e'.
Proof.
  intros e T Htyp.
  remember [] as G eqn:HeqG.
  revert HeqG.
  induction Htyp; intros HeqG; subst.
  - left. constructor.
  - simpl in H. discriminate.
  - destruct (IHHtyp1 eq_refl) as [Hval1 | [e1' Hstep1]].
    + right.
      exists (subst z e1 e2).
      apply ST_LetBeta.
      * exact Hval1.
      * unfold closed.
        exact (typing_implies_closed_at [] e1 U Htyp1).
    + right.
      exists (E_Let z e1' e2).
      apply ST_Let1.
      exact Hstep1.
  - left. constructor.
  - destruct (IHHtyp1 eq_refl) as [Hval1 | [e1' Hstep1]].
    + destruct (IHHtyp2 eq_refl) as [Hval2 | [e2' Hstep2]].
      * destruct (canonical_forms_arrow _ _ _ Hval1 Htyp1) as [z [e_body Heq]].
        subst.
        right.
        exists (subst z e2 e_body).
        apply ST_AppBeta.
        -- exact Hval2.
        -- unfold closed.
           exact (typing_implies_closed_at [] e2 U Htyp2).
      * right.
        exists (E_App e1 e2').
        apply ST_App2.
        -- exact Hval1.
        -- exact Hstep2.
    + right.
      exists (E_App e1' e2).
      apply ST_App1.
      exact Hstep1.
Qed.

Theorem op_subject_reduction :
  forall G e T e',
    has_type G e T ->
    step e e' ->
    has_type G e' T.
Proof.
  intros G e T e' Htyp Hstep.
  generalize dependent e'.
  induction Htyp; intros e' Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + eapply T_Let.
      * match goal with
        | Hs : step e1 _ |- _ => exact (IHHtyp1 _ Hs)
        end.
      * exact Htyp2.
    + eapply subst_preserves; eauto.
      eapply closed_typed_empty; eauto.
  - inversion Hstep.
  - inversion Hstep; subst.
    + eapply T_App.
      * match goal with
        | Hs : step e1 _ |- _ => exact (IHHtyp1 _ Hs)
        end.
      * exact Htyp2.
    + eapply T_App.
      * exact Htyp1.
      * match goal with
        | Hs : step e2 _ |- _ => exact (IHHtyp2 _ Hs)
        end.
    + inversion Htyp1; subst.
      eapply subst_preserves; eauto.
      eapply closed_typed_empty; eauto.
Qed.

(** * Further properties (2026-04-20) *)

(** Values do not step.  Corollary of progress + canonical forms. *)
Theorem values_do_not_step :
  forall v e',
    value v ->
    ~ step v e'.
Proof.
  intros v e' Hval Hstep.
  inversion Hval; subst; inversion Hstep.
Qed.

(** Canonical forms for the Nat type: values of type Nat are constants. *)
Theorem canonical_forms_nat :
  forall v,
    value v ->
    has_type [] v T_Nat ->
    exists n, v = E_Const n.
Proof.
  intros v Hval Htyp.
  inversion Hval; subst.
  - exists n. reflexivity.
  - inversion Htyp.
Qed.

(** Multi-step preservation: multi-step reduction preserves typing. *)
Inductive multi_step : expr -> expr -> Prop :=
  | MStep_refl : forall e, multi_step e e
  | MStep_cons : forall e e' e'',
      step e e' -> multi_step e' e'' -> multi_step e e''.

Theorem op_multi_preservation :
  forall G e T e',
    has_type G e T ->
    multi_step e e' ->
    has_type G e' T.
Proof.
  intros G e T e' Htyp Hms. generalize dependent T. generalize dependent G.
  induction Hms; intros G T Htyp.
  - exact Htyp.
  - apply IHHms. eapply op_subject_reduction; eauto.
Qed.

(** Multi-step is reflexive and transitive. *)
Theorem multi_step_refl : forall e, multi_step e e.
Proof. exact MStep_refl. Qed.

Theorem multi_step_trans :
  forall e1 e2 e3,
    multi_step e1 e2 ->
    multi_step e2 e3 ->
    multi_step e1 e3.
Proof.
  intros e1 e2 e3 H1. induction H1 as [e|e a b Hs Ht IH]; intros H2.
  - exact H2.
  - eapply MStep_cons; [exact Hs | apply IH; exact H2].
Qed.

(** Soundness of the type system: well-typed closed terms don't get
    stuck.  A well-typed term either terminates at a value or can
    take another step. *)
Theorem op_type_soundness :
  forall e T e',
    has_type [] e T ->
    multi_step e e' ->
    value e' \/ exists e'', step e' e''.
Proof.
  intros e T e' Htyp Hms.
  assert (Htyp' : has_type [] e' T)
    by (eapply op_multi_preservation; eauto).
  apply (op_progress e' T Htyp').
Qed.

(** ** Further value / type properties (2026-04-20) *)

(** Values are preserved by multi_step where the target is also a value
    (trivial: each value has the form E_Const or E_Lam, and steps from
    these are impossible). *)
Theorem value_multi_step_refl :
  forall v, value v -> multi_step v v.
Proof. intros v _. apply MStep_refl. Qed.

(** Multi-step from a value: v multi-steps only to itself. *)
Theorem value_multi_step_fixed :
  forall v v',
    value v ->
    multi_step v v' ->
    v = v'.
Proof.
  intros v v' Hval Hms. induction Hms as [|e e' e'' Hstep _ IH].
  - reflexivity.
  - exfalso. apply (values_do_not_step e e' Hval Hstep).
Qed.

(** E_Const is a value constructor (named alias). *)
Lemma const_is_value : forall n, value (E_Const n).
Proof. intros n. apply V_Const. Qed.

(** E_Lam is a value constructor (named alias). *)
Lemma lam_is_value : forall x T e, value (E_Lam x T e).
Proof. intros x T e. apply V_Lam. Qed.

(** Zero-step reflexivity for multi_step. *)
Lemma multi_step_zero : forall e, multi_step e e.
Proof. apply multi_step_refl. Qed.
