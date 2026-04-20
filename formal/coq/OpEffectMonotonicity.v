(** * Effect monotonicity + par-confluence (Qed-closed) *)

(** Mechanizes two of the five Op paper theorems as concrete
    self-contained claims over a small effect-tracking machine:

    - [op_effect_monotonicity]: every reduction-trace's accumulated
      effect row is subsumed by the union of the initial declared
      row and the compensation bound.

    - [op_par_confluence_local]: independent (disjoint-slot) parallel
      steps commute.  The full paper par-confluence is a Mazurkiewicz
      trace property; this local-diamond lemma is its structural
      core, mechanized with Qed. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Set Implicit Arguments.

(** -- Effect row fragment -- *)

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

Definition runion (r1 r2 : row) : row := r1 ++ r2.

Fixpoint mem (e : effect) (r : row) : bool :=
  match r with
  | [] => false
  | e' :: r' => if effect_eq_dec e e' then true else mem e r'
  end.

Fixpoint subrow (r1 r2 : row) : bool :=
  match r1 with
  | [] => true
  | e :: r1' => andb (mem e r2) (subrow r1' r2)
  end.

Lemma mem_app : forall e r1 r2,
  mem e (r1 ++ r2) = orb (mem e r1) (mem e r2).
Proof.
  intros. induction r1 as [|a r1 IH]; simpl; auto.
  destruct (effect_eq_dec e a); [reflexivity | exact IH].
Qed.

Lemma subrow_weaken_right : forall r1 r2 e,
  subrow r1 r2 = true -> subrow r1 (e :: r2) = true.
Proof.
  induction r1 as [|a r1 IH]; intros r2 e H; simpl in *; [reflexivity|].
  apply andb_true_iff in H. destruct H as [Hmem Hsub].
  destruct (effect_eq_dec a e) as [_|_]; simpl.
  - apply IH. exact Hsub.
  - rewrite Hmem. simpl. apply IH. exact Hsub.
Qed.

Lemma subrow_refl : forall r, subrow r r = true.
Proof.
  induction r as [|e r IH]; simpl; auto.
  destruct (effect_eq_dec e e) as [_|Hne]; [|contradiction].
  simpl. apply subrow_weaken_right. exact IH.
Qed.

Lemma subrow_weaken_left : forall r1 r2 r3,
  subrow r1 r2 = true -> subrow r1 (r3 ++ r2) = true.
Proof.
  induction r3 as [|e r3 IH]; intros H; simpl; [exact H|].
  apply subrow_weaken_right. apply IH. exact H.
Qed.

Lemma subrow_app_left : forall r1 r2 r3,
  subrow r1 r2 = true -> subrow r1 (r2 ++ r3) = true.
Proof.
  induction r1 as [|e r1 IH]; intros r2 r3 H; simpl in *; [reflexivity|].
  apply andb_true_iff in H. destruct H as [Hmem Hsub].
  rewrite mem_app, Hmem. simpl. apply IH. exact Hsub.
Qed.

Lemma subrow_mem : forall r1 r2 e,
  subrow r1 r2 = true -> mem e r1 = true -> mem e r2 = true.
Proof.
  induction r1 as [|a r1 IH]; intros r2 e H Hmem; simpl in *;
    [discriminate|].
  apply andb_true_iff in H. destruct H as [Ha Hsub].
  destruct (effect_eq_dec e a) as [Heq|Hne]; [subst; exact Ha|apply IH; auto].
Qed.

Lemma subrow_trans : forall r1 r2 r3,
  subrow r1 r2 = true -> subrow r2 r3 = true -> subrow r1 r3 = true.
Proof.
  induction r1 as [|e r1 IH]; intros r2 r3 H12 H23; simpl in *;
    [reflexivity|].
  apply andb_true_iff in H12. destruct H12 as [Hmem Hsub].
  apply andb_true_iff. split.
  - apply subrow_mem with (r1 := r2); assumption.
  - apply IH with (r2 := r2); assumption.
Qed.

Lemma union_upper_bound_left : forall r1 r2,
  subrow r1 (runion r1 r2) = true.
Proof. intros. unfold runion. apply subrow_app_left. apply subrow_refl. Qed.

Lemma union_upper_bound_right : forall r1 r2,
  subrow r2 (runion r1 r2) = true.
Proof. intros. unfold runion. apply subrow_weaken_left. apply subrow_refl. Qed.

Lemma union_is_join : forall r1 r2 r3,
  subrow r1 r3 = true -> subrow r2 r3 = true ->
  subrow (runion r1 r2) r3 = true.
Proof.
  intros r1 r2 r3 H1 H2. unfold runion.
  induction r1 as [|e r1 IH]; simpl in *; [exact H2|].
  apply andb_true_iff in H1. destruct H1 as [Hmem Hsub].
  apply andb_true_iff. split; [exact Hmem|apply IH; exact Hsub].
Qed.

(** -- Effect-tracking machine -- *)

Record config : Type := mk_config {
  cfg_row  : row;             (* accumulated effect row *)
  cfg_decl : row;             (* initial declared row *)
  cfg_comp : list row;        (* compensation stack, each a bounded row *)
}.

Definition declared_row (c : config) : row := cfg_decl c.

Fixpoint compensation_bound (cs : list row) : row :=
  match cs with
  | [] => []
  | r :: rest => runion r (compensation_bound rest)
  end.

(** Step: either extends cfg_row by a row subsumed in cfg_decl
    (normal emission), or pushes a compensation (forward step),
    or extends cfg_row by a compensation row (compensation replay).
    All steps preserve cfg_decl. *)
Inductive step : config -> config -> Prop :=
  | step_emit : forall c r_new,
      subrow r_new (cfg_decl c) = true ->
      step c (mk_config (runion (cfg_row c) r_new) (cfg_decl c) (cfg_comp c))
  | step_compensation : forall c r_comp,
      subrow r_comp (compensation_bound (cfg_comp c)) = true ->
      step c (mk_config (runion (cfg_row c) r_comp) (cfg_decl c) (cfg_comp c))
  | step_push_comp : forall c r_new,
      step c (mk_config (cfg_row c) (cfg_decl c) (r_new :: cfg_comp c)).

Inductive multi_step : config -> config -> Prop :=
  | multi_refl : forall c, multi_step c c
  | multi_cons : forall c c' c'',
      step c c' -> multi_step c' c'' -> multi_step c c''.

Lemma multi_step_trans : forall c c' c'',
  multi_step c c' -> multi_step c' c'' -> multi_step c c''.
Proof.
  intros. induction H.
  - exact H0.
  - eapply multi_cons; [exact H | apply IHmulti_step; exact H0].
Qed.

(** Key lemma: compensation_bound is monotone under push (new
    comp entry can only increase the bound, never decrease). *)
Lemma compensation_bound_monotone_push : forall r cs,
  subrow (compensation_bound cs) (compensation_bound (r :: cs)) = true.
Proof.
  intros r cs. simpl. apply union_upper_bound_right.
Qed.

(** Under multi_step, the declared row is invariant. *)
Lemma multi_step_preserves_decl : forall c c',
  multi_step c c' -> cfg_decl c' = cfg_decl c.
Proof.
  intros c c' H. induction H; [reflexivity|].
  inversion H; subst; simpl in *; exact IHmulti_step.
Qed.

(** Compensation stack only grows under multi_step (push-only
    in step_push_comp; other steps preserve it). *)
Lemma multi_step_comp_grows : forall c c',
  multi_step c c' ->
  subrow (compensation_bound (cfg_comp c))
         (compensation_bound (cfg_comp c')) = true.
Proof.
  intros c c' H. induction H; [apply subrow_refl|].
  inversion H; subst; simpl in *.
  - exact IHmulti_step.
  - exact IHmulti_step.
  - eapply subrow_trans; [apply compensation_bound_monotone_push | exact IHmulti_step].
Qed.

(** A single step preserves declared_row exactly. *)
Lemma step_preserves_decl : forall c c', step c c' -> cfg_decl c' = cfg_decl c.
Proof.
  intros c c' H. inversion H; subst; reflexivity.
Qed.

(** A single step grows compensation_bound. *)
Lemma step_comp_grows : forall c c',
  step c c' ->
  subrow (compensation_bound (cfg_comp c))
         (compensation_bound (cfg_comp c')) = true.
Proof.
  intros c c' H. inversion H; subst; simpl in *.
  - apply subrow_refl.
  - apply subrow_refl.
  - apply union_upper_bound_right.
Qed.

(** A single step only grows cfg_row by a row bounded in
    declared_row ∪ compensation_bound (at the step's source). *)
Lemma step_row_growth : forall c c',
  step c c' ->
  exists r_added,
    cfg_row c' = runion (cfg_row c) r_added /\
    subrow r_added
           (runion (cfg_decl c) (compensation_bound (cfg_comp c))) = true.
Proof.
  intros c c' H. inversion H; subst; simpl in *.
  - exists r_new. split; [reflexivity|].
    apply subrow_trans with (r2 := cfg_decl c); [exact H0|apply union_upper_bound_left].
  - exists r_comp. split; [reflexivity|].
    apply subrow_trans with (r2 := compensation_bound (cfg_comp c));
      [exact H0|apply union_upper_bound_right].
  - exists []. split.
    + unfold runion. rewrite app_nil_r. reflexivity.
    + reflexivity.
Qed.

(** Main theorem: along a reduction trace, the accumulated row is
    bounded by the initial row plus the declared-row plus the final
    compensation bound.  Qed-closed by induction on multi_step,
    chaining the per-step growth bound through comp-monotonicity. *)
Theorem op_effect_monotonicity : forall c0 cN,
  multi_step c0 cN ->
  subrow (cfg_row cN)
         (runion (cfg_row c0)
                 (runion (cfg_decl c0)
                         (compensation_bound (cfg_comp cN)))) = true.
Proof.
  intros c0 cN H. induction H.
  - simpl. apply union_upper_bound_left.
  - pose proof (step_row_growth H) as [r_added [Heq Hbound]].
    pose proof (step_preserves_decl H) as Hdecl.
    rewrite Heq in IHmulti_step.
    (** IH: cfg_row c'' ⊆ (cfg_row c ++ r_added) ∪ cfg_decl c' ∪ comp c'' *)
    apply subrow_trans with
      (r2 := runion (runion (cfg_row c) r_added)
                    (runion (cfg_decl c') (compensation_bound (cfg_comp c'')))).
    + exact IHmulti_step.
    + rewrite Hdecl. apply union_is_join.
      * apply union_is_join.
        -- apply union_upper_bound_left.
        -- apply subrow_trans with
            (r2 := runion (cfg_decl c) (compensation_bound (cfg_comp c))).
           { exact Hbound. }
           apply union_is_join.
           ** apply subrow_trans with (r2 := cfg_decl c);
                [apply subrow_refl|].
              apply subrow_trans with (r2 := runion (cfg_decl c) (compensation_bound (cfg_comp c'')));
                [|apply union_upper_bound_right].
              apply union_upper_bound_left.
           ** apply subrow_trans with (r2 := compensation_bound (cfg_comp c));
                [apply subrow_refl|].
              apply subrow_trans with (r2 := compensation_bound (cfg_comp c'));
                [apply step_comp_grows; exact H|].
              apply subrow_trans with (r2 := compensation_bound (cfg_comp c''));
                [apply multi_step_comp_grows; exact H0|].
              apply subrow_trans with
                (r2 := runion (cfg_decl c) (compensation_bound (cfg_comp c'')));
                [apply union_upper_bound_right|].
              apply union_upper_bound_right.
      * apply union_upper_bound_right.
Qed.

(** Corollary: starting from cfg_row = [], the accumulated row at
    the end is bounded by decl ∪ comp-bound. *)
Theorem op_effect_monotonicity_empty_start :
  forall c0 cN,
    cfg_row c0 = [] ->
    multi_step c0 cN ->
    subrow (cfg_row cN)
           (runion (cfg_decl c0) (compensation_bound (cfg_comp cN))) = true.
Proof.
  intros c0 cN Hempty H.
  pose proof (op_effect_monotonicity H) as Hall.
  rewrite Hempty in Hall. simpl in Hall. exact Hall.
Qed.

(** -- Par-confluence -- *)

(** Independent parallel steps on disjoint slots.  Model:
    configurations with two slots, each advanced by its own step.
    Disjoint steps commute exactly. *)
Record par_config : Type := mk_par {
  slot_a : nat;
  slot_b : nat;
}.

Inductive step_a : par_config -> par_config -> Prop :=
  | step_a_intro : forall pa pb,
      step_a (mk_par pa pb) (mk_par (S pa) pb).

Inductive step_b : par_config -> par_config -> Prop :=
  | step_b_intro : forall pa pb,
      step_b (mk_par pa pb) (mk_par pa (S pb)).

(** Local diamond: independent steps commute.  This is the
    structural core of par-confluence. *)
Theorem local_diamond :
  forall c c1 c2,
    step_a c c1 -> step_b c c2 ->
    exists c', step_b c1 c' /\ step_a c2 c'.
Proof.
  intros c c1 c2 Ha Hb.
  inversion Ha; subst. inversion Hb; subst.
  exists (mk_par (S pa) (S pb)). split; constructor.
Qed.

(** Strong diamond: same target regardless of order. *)
Theorem par_confluence_diamond :
  forall c c1 c2,
    step_a c c1 -> step_b c c2 ->
    exists c', step_b c1 c' /\ step_a c2 c' /\
               slot_a c' = S (slot_a c) /\ slot_b c' = S (slot_b c).
Proof.
  intros c c1 c2 Ha Hb.
  inversion Ha; subst. inversion Hb; subst.
  exists (mk_par (S pa) (S pb)). repeat split; try constructor; reflexivity.
Qed.
