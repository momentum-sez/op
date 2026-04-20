From Stdlib Require Import List Bool.
Import ListNotations.

Set Implicit Arguments.

Inductive effect : Type :=
  | E_SovereignWrite
  | E_IdentityMutation
  | E_FiscalTransfer
  | E_SanctionsCheck
  | E_GovernanceRequest
  | E_DocumentGeneration
  | E_ExternalRead
  | E_ProofEmit
  | E_Await.

Definition effect_eq_dec : forall e1 e2 : effect, {e1 = e2} + {e1 <> e2}.
Proof. decide equality. Defined.

Definition row : Type := list effect.

Definition rempty : row := [].

Fixpoint mem (e : effect) (r : row) : bool :=
  match r with
  | [] => false
  | e' :: r' => if effect_eq_dec e e' then true else mem e r'
  end.

Definition runion (r1 r2 : row) : row := r1 ++ r2.

Fixpoint subrow (r1 r2 : row) : bool :=
  match r1 with
  | [] => true
  | e :: r1' => andb (mem e r2) (subrow r1' r2)
  end.

Lemma mem_app : forall e r1 r2,
  mem e (r1 ++ r2) = orb (mem e r1) (mem e r2).
Proof.
  intros e r1 r2. induction r1 as [|a r1 IH]; simpl.
  - reflexivity.
  - destruct (effect_eq_dec e a); [reflexivity | exact IH].
Qed.

Lemma subrow_weaken_right : forall r1 r2 e,
  subrow r1 r2 = true ->
  subrow r1 (e :: r2) = true.
Proof.
  induction r1 as [|a r1 IH]; intros r2 e H; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H. destruct H as [Hmem Hsub].
    destruct (effect_eq_dec a e) as [_|_]; simpl.
    + apply IH. exact Hsub.
    + rewrite Hmem. simpl. apply IH. exact Hsub.
Qed.

Lemma subrow_refl : forall r, subrow r r = true.
Proof.
  induction r as [|e r IH]; simpl; auto.
  destruct (effect_eq_dec e e) as [_|Hne]; [| contradiction].
  simpl. apply subrow_weaken_right. exact IH.
Qed.

Lemma subrow_app_left : forall r1 r2 r3,
  subrow r1 r2 = true ->
  subrow r1 (r2 ++ r3) = true.
Proof.
  induction r1 as [|e r1 IH]; intros r2 r3 H; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H. destruct H as [Hmem Hsub].
    rewrite mem_app. rewrite Hmem. simpl.
    apply IH. exact Hsub.
Qed.

Lemma subrow_union_right : forall r r1 r2,
  subrow r r1 = true ->
  subrow r (runion r1 r2) = true.
Proof.
  intros r r1 r2 H. unfold runion. apply subrow_app_left. exact H.
Qed.

Theorem union_upper_bound_left : forall r1 r2,
  subrow r1 (runion r1 r2) = true.
Proof.
  intros r1 r2. apply subrow_union_right. apply subrow_refl.
Qed.

Lemma subrow_weaken_left : forall r1 r2 r3,
  subrow r1 r2 = true ->
  subrow r1 (r3 ++ r2) = true.
Proof.
  induction r3 as [|e r3 IH]; intros H; simpl.
  - exact H.
  - apply subrow_weaken_right. apply IH. exact H.
Qed.

Theorem union_upper_bound_right : forall r1 r2,
  subrow r2 (runion r1 r2) = true.
Proof.
  intros r1 r2. unfold runion.
  apply subrow_weaken_left. apply subrow_refl.
Qed.

Lemma subrow_mem : forall r1 r2 e,
  subrow r1 r2 = true ->
  mem e r1 = true ->
  mem e r2 = true.
Proof.
  induction r1 as [|a r1 IH]; intros r2 e H Hmem; simpl in *.
  - discriminate.
  - apply andb_true_iff in H. destruct H as [Ha Hsub].
    destruct (effect_eq_dec e a) as [Heq|Hne].
    + subst. exact Ha.
    + apply IH; assumption.
Qed.

Lemma subrow_trans : forall r1 r2 r3,
  subrow r1 r2 = true ->
  subrow r2 r3 = true ->
  subrow r1 r3 = true.
Proof.
  induction r1 as [|e r1 IH]; intros r2 r3 H12 H23; simpl in *.
  - reflexivity.
  - apply andb_true_iff in H12. destruct H12 as [Hmem Hsub].
    apply andb_true_iff. split.
    + apply subrow_mem with (r1 := r2); assumption.
    + apply IH with (r2 := r2); assumption.
Qed.

Theorem union_is_join : forall r1 r2 r3,
  subrow r1 r3 = true ->
  subrow r2 r3 = true ->
  subrow (runion r1 r2) r3 = true.
Proof.
  intros r1 r2 r3 H1 H2. unfold runion.
  induction r1 as [|e r1 IH]; simpl in *.
  - exact H2.
  - apply andb_true_iff in H1. destruct H1 as [Hmem Hsub].
    apply andb_true_iff. split.
    + exact Hmem.
    + apply IH. exact Hsub.
Qed.

Record config : Type := mk_config {
  cfg_expr : nat;
  cfg_row : row;
  cfg_comp : list row;
}.

Definition declared_row (c : config) : row := cfg_row c.

Fixpoint compensation_bound (cs : list row) : row :=
  match cs with
  | [] => rempty
  | r :: rest => runion r (compensation_bound rest)
  end.

Inductive step : config -> config -> Prop :=
  | step_pure : forall e r comp r',
      subrow r' (compensation_bound comp) = true ->
      step (mk_config e r comp) (mk_config (S e) (runion r r') comp)
  | step_push_comp : forall e r comp r',
      subrow r' (compensation_bound comp) = true ->
      step (mk_config e r comp) (mk_config (S e) r (r' :: comp)).

Inductive multi_step : config -> config -> Prop :=
  | multi_refl : forall c, multi_step c c
  | multi_cons : forall c c' c'',
      step c c' ->
      multi_step c' c'' ->
      multi_step c c''.

Definition trace_effect_row (_c0 cN : config) : row := cfg_row cN.

Lemma step_preserves_bounds :
  forall c c' row_bound comp_bound,
    step c c' ->
    subrow (cfg_row c) (runion row_bound comp_bound) = true ->
    subrow (compensation_bound (cfg_comp c)) comp_bound = true ->
    subrow (cfg_row c') (runion row_bound comp_bound) = true /\
    subrow (compensation_bound (cfg_comp c')) comp_bound = true.
Proof.
  intros c c' row_bound comp_bound Hstep Hrow Hcomp.
  destruct Hstep as [e r comp r' Hr' | e r comp r' Hr']; simpl in *.
  - split.
    + apply union_is_join.
      * exact Hrow.
      * eapply subrow_trans.
        -- exact Hr'.
        -- eapply subrow_trans.
           ++ exact Hcomp.
           ++ apply union_upper_bound_right.
    + exact Hcomp.
  - split.
    + exact Hrow.
    + apply union_is_join.
      * eapply subrow_trans.
        -- exact Hr'.
        -- exact Hcomp.
      * exact Hcomp.
Qed.

Lemma multi_step_preserves_bounds :
  forall c0 cN,
    multi_step c0 cN ->
    forall row_bound comp_bound,
      subrow (cfg_row c0) (runion row_bound comp_bound) = true ->
      subrow (compensation_bound (cfg_comp c0)) comp_bound = true ->
      subrow (cfg_row cN) (runion row_bound comp_bound) = true /\
      subrow (compensation_bound (cfg_comp cN)) comp_bound = true.
Proof.
  intros c0 cN Hmulti.
  induction Hmulti as [c|c c' c'' Hstep Hmulti IH]; intros row_bound comp_bound Hrow Hcomp.
  - split; assumption.
  - assert (Hbounds :
        subrow (cfg_row c') (runion row_bound comp_bound) = true /\
        subrow (compensation_bound (cfg_comp c')) comp_bound = true).
    { eapply step_preserves_bounds; eauto. }
    destruct Hbounds as [Hrow' Hcomp'].
    apply IH; assumption.
Qed.

Theorem op_effect_monotonicity :
  forall c0 cN,
    multi_step c0 cN ->
    subrow (trace_effect_row c0 cN)
           (runion (declared_row c0) (compensation_bound (cfg_comp c0))) = true.
Proof.
  intros c0 cN Hmulti.
  unfold trace_effect_row, declared_row.
  assert (Hbounds :
      subrow (cfg_row cN)
        (runion (cfg_row c0) (compensation_bound (cfg_comp c0))) = true /\
      subrow (compensation_bound (cfg_comp cN))
        (compensation_bound (cfg_comp c0)) = true).
  { eapply multi_step_preserves_bounds; eauto.
    - apply union_upper_bound_left.
    - apply subrow_refl. }
  destruct Hbounds as [Hrow _].
  exact Hrow.
Qed.
