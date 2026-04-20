From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Strings.String.
Require Import CompilationSoundness.

Import ListNotations.
Open Scope string_scope.

Set Implicit Arguments.

(** * OpMetaTheory.v

    A minimal core metatheory for the admissible Op fragment.

    The repository previously mechanized the nine verdict-preservation
    cases in [CompilationSoundness.v] separately. This file adds two
    pieces of structure around that result:

    - a small core typing and reduction relation carrying the paper's
      context / effect-row / compliance-context discipline, enough to
      close the standard structural lemmas and the conservation-style
      monotonicity results; and
    - a single admissible-fragment wrapper theorem that lifts the nine
      case-specific verdict-preservation results into one theorem over a
      sum of the admissible source and target shapes.

    The extension is intentionally minimal. It does not replace the
    abstract statement-only targets in [OpPaperTargets.v]; it gives the
    paper a concrete closed fragment with named theorems. *)

Inductive core_verdict : Type :=
  | CV_Compliant
  | CV_Review
  | CV_SanctionsBlocked.

Record core_effect_row : Type := mk_row {
  row_prelude : bool;
  row_sanctions : bool;
  row_commit : bool;
  row_release : bool
}.

Definition row_empty : core_effect_row :=
  mk_row false false false false.

Definition row_sanctions_only : core_effect_row :=
  mk_row false true false false.

Definition row_commit_only : core_effect_row :=
  mk_row false false true false.

Definition row_release_only : core_effect_row :=
  mk_row false false false true.

Definition row_join (r1 r2 : core_effect_row) : core_effect_row :=
  mk_row
    (orb (row_prelude r1) (row_prelude r2))
    (orb (row_sanctions r1) (row_sanctions r2))
    (orb (row_commit r1) (row_commit r2))
    (orb (row_release r1) (row_release r2)).

Definition row_subsumed (r1 r2 : core_effect_row) : Prop :=
  (row_prelude r1 = true -> row_prelude r2 = true) /\
  (row_sanctions r1 = true -> row_sanctions r2 = true) /\
  (row_commit r1 = true -> row_commit r2 = true) /\
  (row_release r1 = true -> row_release r2 = true).

Lemma row_subsumed_refl :
  forall r,
    row_subsumed r r.
Proof.
  intros [a b c d]; repeat split; tauto.
Qed.

Lemma row_subsumed_trans :
  forall r1 r2 r3,
    row_subsumed r1 r2 ->
    row_subsumed r2 r3 ->
    row_subsumed r1 r3.
Proof.
  intros [a1 b1 c1 d1] [a2 b2 c2 d2] [a3 b3 c3 d3].
  intros [Hp1 [Hs1 [Hc1 Hr1]]] [Hp2 [Hs2 [Hc2 Hr2]]].
  repeat split; intros H.
  - apply Hp2, Hp1, H.
  - apply Hs2, Hs1, H.
  - apply Hc2, Hc1, H.
  - apply Hr2, Hr1, H.
Qed.

Lemma row_subsumed_join_left :
  forall r1 r2,
    row_subsumed r1 (row_join r1 r2).
Proof.
  intros [a1 b1 c1 d1] [a2 b2 c2 d2].
  repeat split; simpl; intros H; rewrite H; reflexivity.
Qed.

Lemma row_subsumed_join_right :
  forall r1 r2,
    row_subsumed r2 (row_join r1 r2).
Proof.
  intros [a1 b1 c1 d1] [a2 b2 c2 d2].
  repeat split; simpl; intros H.
  - destruct a1; simpl; try reflexivity; exact H.
  - destruct b1; simpl; try reflexivity; exact H.
  - destruct c1; simpl; try reflexivity; exact H.
  - destruct d1; simpl; try reflexivity; exact H.
Qed.

Lemma row_subsumed_join_mono :
  forall r1 r2 s1 s2,
    row_subsumed r1 s1 ->
    row_subsumed r2 s2 ->
    row_subsumed (row_join r1 r2) (row_join s1 s2).
Proof.
  intros [a1 b1 c1 d1] [a2 b2 c2 d2] [a3 b3 c3 d3] [a4 b4 c4 d4].
  intros [Hp1 [Hs1 [Hc1 Hr1]]] [Hp2 [Hs2 [Hc2 Hr2]]].
  repeat split; simpl; intros H.
  - destruct a3, a4; simpl.
    all: destruct a1, a2; simpl in *; try discriminate; try reflexivity;
      firstorder.
  - destruct b3, b4; simpl.
    all: destruct b1, b2; simpl in *; try discriminate; try reflexivity;
      firstorder.
  - destruct c3, c4; simpl.
    all: destruct c1, c2; simpl in *; try discriminate; try reflexivity;
      firstorder.
  - destruct d3, d4; simpl.
    all: destruct d1, d2; simpl in *; try discriminate; try reflexivity;
      firstorder.
Qed.

Inductive core_compliance_ctx : Type :=
  | KClean
  | KBlocked.

Definition compliance_le (k1 k2 : core_compliance_ctx) : Prop :=
  match k1, k2 with
  | KBlocked, _ => True
  | KClean, KClean => True
  | KClean, KBlocked => False
  end.

Inductive core_ty : Type :=
  | CT_Unit
  | CT_Bool
  | CT_Int
  | CT_String
  | CT_Verdict
  | CT_Locked : core_ty -> string -> core_effect_row -> core_ty.

Inductive core_expr : Type :=
  | CE_Var : string -> core_expr
  | CE_Unit : core_expr
  | CE_Bool : bool -> core_expr
  | CE_Int : nat -> core_expr
  | CE_Str : string -> core_expr
  | CE_Verdict : core_verdict -> core_expr
  | CE_Let : string -> core_expr -> core_expr -> core_expr
  | CE_Sanctions : core_verdict -> core_expr
  | CE_Locked : core_ty -> string -> core_effect_row -> core_expr
  | CE_Commit : core_expr -> core_expr
  | CE_Release : core_expr -> core_expr.

Inductive core_value : core_expr -> Prop :=
  | CV_UnitV :
      core_value CE_Unit
  | CV_BoolV :
      forall b, core_value (CE_Bool b)
  | CV_IntV :
      forall n, core_value (CE_Int n)
  | CV_StrV :
      forall s, core_value (CE_Str s)
  | CV_VerdictV :
      forall v, core_value (CE_Verdict v)
  | CV_LockedV :
      forall T omega eps, core_value (CE_Locked T omega eps).

Fixpoint core_subst (x : string) (v : core_expr) (e : core_expr) : core_expr :=
  match e with
  | CE_Var y =>
      if String.eqb x y then v else CE_Var y
  | CE_Unit => CE_Unit
  | CE_Bool b => CE_Bool b
  | CE_Int n => CE_Int n
  | CE_Str s => CE_Str s
  | CE_Verdict vv => CE_Verdict vv
  | CE_Let y e1 e2 =>
      CE_Let y (core_subst x v e1)
               (if String.eqb x y then e2 else core_subst x v e2)
  | CE_Sanctions vv => CE_Sanctions vv
  | CE_Locked T omega eps => CE_Locked T omega eps
  | CE_Commit e1 => CE_Commit (core_subst x v e1)
  | CE_Release e1 => CE_Release (core_subst x v e1)
  end.

Inductive appears_free_in : string -> core_expr -> Prop :=
  | AF_Var :
      forall x,
        appears_free_in x (CE_Var x)
  | AF_LetRhs :
      forall x y e1 e2,
        appears_free_in x e1 ->
        appears_free_in x (CE_Let y e1 e2)
  | AF_LetBody :
      forall x y e1 e2,
        x <> y ->
        appears_free_in x e2 ->
        appears_free_in x (CE_Let y e1 e2)
  | AF_Commit :
      forall x e,
        appears_free_in x e ->
        appears_free_in x (CE_Commit e)
  | AF_Release :
      forall x e,
        appears_free_in x e ->
        appears_free_in x (CE_Release e).

Fixpoint body_row (e : core_expr) : core_effect_row :=
  match e with
  | CE_Var _ => row_empty
  | CE_Unit => row_empty
  | CE_Bool _ => row_empty
  | CE_Int _ => row_empty
  | CE_Str _ => row_empty
  | CE_Verdict _ => row_empty
  | CE_Let _ e1 e2 => row_join (body_row e1) (body_row e2)
  | CE_Sanctions _ => row_sanctions_only
  | CE_Locked _ _ _ => row_empty
  | CE_Commit _ => row_commit_only
  | CE_Release _ => row_release_only
  end.

Definition core_context := string -> option core_ty.

Definition empty_ctx : core_context :=
  fun _ => None.

Definition ctx_extend (Gamma : core_context) (x : string) (T : core_ty)
  : core_context :=
  fun y => if String.eqb x y then Some T else Gamma y.

Lemma ctx_extend_eq :
  forall Gamma x T,
    ctx_extend Gamma x T x = Some T.
Proof.
  intros. unfold ctx_extend. now rewrite String.eqb_refl.
Qed.

Lemma ctx_extend_neq :
  forall Gamma x y T,
    x <> y ->
    ctx_extend Gamma x T y = Gamma y.
Proof.
  intros Gamma x y T Hneq.
  unfold ctx_extend.
  destruct (String.eqb_spec x y); congruence.
Qed.

Lemma ctx_extend_shadow :
  forall Gamma x T1 T2 y,
    ctx_extend (ctx_extend Gamma x T1) x T2 y =
    ctx_extend Gamma x T2 y.
Proof.
  intros Gamma x T1 T2 y.
  unfold ctx_extend.
  destruct (String.eqb_spec x y); reflexivity.
Qed.

Inductive core_has_type :
  core_context ->
  core_compliance_ctx ->
  core_expr ->
  core_ty ->
  core_effect_row ->
  core_compliance_ctx ->
  Prop :=
  | CT_Var :
      forall Gamma k x T,
        Gamma x = Some T ->
        core_has_type Gamma k (CE_Var x) T row_empty k
  | CT_UnitI :
      forall Gamma k,
        core_has_type Gamma k CE_Unit CT_Unit row_empty k
  | CT_BoolI :
      forall Gamma k b,
        core_has_type Gamma k (CE_Bool b) CT_Bool row_empty k
  | CT_IntI :
      forall Gamma k n,
        core_has_type Gamma k (CE_Int n) CT_Int row_empty k
  | CT_StrI :
      forall Gamma k s,
        core_has_type Gamma k (CE_Str s) CT_String row_empty k
  | CT_VerdictI :
      forall Gamma k v,
        core_has_type Gamma k (CE_Verdict v) CT_Verdict row_empty k
  | CT_LetI :
      forall Gamma k x e1 e2 T1 T2 eps1 eps2 k1 k2,
        core_has_type Gamma k e1 T1 eps1 k1 ->
        core_has_type (ctx_extend Gamma x T1) k1 e2 T2 eps2 k2 ->
        core_has_type Gamma k (CE_Let x e1 e2) T2 (row_join eps1 eps2) k2
  | CT_SanctionsBlocked :
      forall Gamma k,
        core_has_type Gamma k (CE_Sanctions CV_SanctionsBlocked)
                      CT_Verdict row_sanctions_only KBlocked
  | CT_SanctionsPass :
      forall Gamma k v,
        v <> CV_SanctionsBlocked ->
        core_has_type Gamma k (CE_Sanctions v)
                      CT_Verdict row_sanctions_only k
  | CT_LockedI :
      forall Gamma k T omega eps,
        core_has_type Gamma k (CE_Locked T omega eps)
                      (CT_Locked T omega eps) row_empty k
  | CT_CommitI :
      forall Gamma k e T omega eps,
        core_has_type Gamma k e (CT_Locked T omega eps) row_empty k ->
        core_has_type Gamma k (CE_Commit e) CT_Unit row_commit_only k
  | CT_ReleaseI :
      forall Gamma k e T omega eps,
        core_has_type Gamma k e (CT_Locked T omega eps) row_empty k ->
        core_has_type Gamma k (CE_Release e) CT_Unit row_release_only k.

Record core_config : Type := mk_core_config {
  cfg_expr : core_expr;
  cfg_kappa : core_compliance_ctx;
  cfg_locked : list string
}.

Fixpoint remove_one (x : string) (locks : list string) : list string :=
  match locks with
  | [] => []
  | y :: ys =>
      if String.string_dec x y then ys else y :: remove_one x ys
  end.

Inductive core_step : core_config -> core_config -> Prop :=
  | CS_Let :
      forall x v e k locks,
        core_value v ->
        core_step (mk_core_config (CE_Let x v e) k locks)
                  (mk_core_config (core_subst x v e) k locks)
  | CS_SanctionsBlocked :
      forall k locks,
        core_step (mk_core_config (CE_Sanctions CV_SanctionsBlocked) k locks)
                  (mk_core_config (CE_Verdict CV_SanctionsBlocked) KBlocked locks)
  | CS_SanctionsPass :
      forall k locks v,
        v <> CV_SanctionsBlocked ->
        core_step (mk_core_config (CE_Sanctions v) k locks)
                  (mk_core_config (CE_Verdict v) k locks)
  | CS_Commit :
      forall k locks T omega eps,
        In omega locks ->
        core_step (mk_core_config (CE_Commit (CE_Locked T omega eps)) k locks)
                  (mk_core_config CE_Unit k (remove_one omega locks))
  | CS_Release :
      forall k locks T omega eps,
        In omega locks ->
        core_step (mk_core_config (CE_Release (CE_Locked T omega eps)) k locks)
                  (mk_core_config CE_Unit k (remove_one omega locks)).

Lemma free_in_context :
  forall Gamma k e T eps k' x,
    core_has_type Gamma k e T eps k' ->
    appears_free_in x e ->
    exists U, Gamma x = Some U.
Proof.
  intros Gamma k e T eps k' x Htyp.
  induction Htyp; intros Hfree.
  - inversion Hfree; subst. eauto.
  - inversion Hfree.
  - inversion Hfree.
  - inversion Hfree.
  - inversion Hfree.
  - inversion Hfree.
  - inversion Hfree; subst.
    + eapply IHHtyp1; eauto.
    + destruct (IHHtyp2 H4) as [U HU].
      exists U.
      rewrite ctx_extend_neq in HU by congruence.
      exact HU.
  - inversion Hfree.
  - inversion Hfree.
  - inversion Hfree.
  - inversion Hfree; subst.
    eapply IHHtyp; eauto.
  - inversion Hfree; subst.
    eapply IHHtyp; eauto.
Qed.

Theorem context_invariance :
  forall Gamma Delta k e T eps k',
    core_has_type Gamma k e T eps k' ->
    (forall x, appears_free_in x e -> Gamma x = Delta x) ->
    core_has_type Delta k e T eps k'.
Proof.
  intros Gamma Delta k e T eps k' Htyp.
  revert Delta.
  induction Htyp; intros Delta Hagree.
  - apply CT_Var.
    rewrite <- (Hagree x).
    + exact H.
    + constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - apply CT_LetI with (T1 := T1) (eps1 := eps1) (k1 := k1).
    + apply IHHtyp1.
      intros x0 Hfree.
      apply Hagree. apply AF_LetRhs. exact Hfree.
    + apply IHHtyp2.
      intros x0 Hfree.
      destruct (String.eqb_spec x x0).
      * subst. rewrite !ctx_extend_eq. reflexivity.
      * rewrite !ctx_extend_neq by congruence.
        apply Hagree. apply AF_LetBody.
        -- congruence.
        -- exact Hfree.
  - constructor.
  - econstructor. exact H.
  - constructor.
  - apply CT_CommitI with (T := T) (omega := omega) (eps := eps).
    apply IHHtyp.
    intros x0 Hfree.
    apply Hagree. constructor. exact Hfree.
  - apply CT_ReleaseI with (T := T) (omega := omega) (eps := eps).
    apply IHHtyp.
    intros x0 Hfree.
    apply Hagree. constructor. exact Hfree.
Qed.

Theorem core_weakening :
  forall Gamma k e T eps k' x U,
    core_has_type Gamma k e T eps k' ->
    Gamma x = None ->
    core_has_type (ctx_extend Gamma x U) k e T eps k'.
Proof.
  intros Gamma k e T eps k' x U Htyp Hnone.
  eapply context_invariance; eauto.
  intros y Hfree.
  destruct (String.eqb_spec x y).
  - subst.
    destruct (free_in_context Htyp Hfree) as [U' HU'].
    rewrite Hnone in HU'. discriminate.
  - rewrite ctx_extend_neq by congruence.
    reflexivity.
Qed.

Theorem core_exchange :
  forall Gamma k e T eps k' x U y V,
    x <> y ->
    core_has_type (ctx_extend (ctx_extend Gamma x U) y V) k e T eps k' ->
    core_has_type (ctx_extend (ctx_extend Gamma y V) x U) k e T eps k'.
Proof.
  intros Gamma k e T eps k' x U y V Hneq Htyp.
  eapply context_invariance; eauto.
  intros z _.
  unfold ctx_extend.
  destruct (String.eqb_spec y z) as [-> | Hy];
    destruct (String.eqb_spec x z) as [-> | Hx];
    try congruence; reflexivity.
Qed.

Theorem core_strengthening :
  forall Gamma k e T eps k' x U,
    core_has_type (ctx_extend Gamma x U) k e T eps k' ->
    ~ appears_free_in x e ->
    core_has_type Gamma k e T eps k'.
Proof.
  intros Gamma k e T eps k' x U Htyp Hnotfree.
  eapply context_invariance; eauto.
  intros y Hfree.
  destruct (String.eqb_spec x y).
  - subst. exfalso. apply Hnotfree. exact Hfree.
  - rewrite ctx_extend_neq by congruence.
    reflexivity.
Qed.

Lemma empty_typed_any_context :
  forall Delta k e T eps k',
    core_has_type empty_ctx k e T eps k' ->
    core_has_type Delta k e T eps k'.
Proof.
  intros Delta k e T eps k' Htyp.
  eapply context_invariance; eauto.
  intros x Hfree.
  exfalso.
  destruct (free_in_context Htyp Hfree) as [U HU].
  discriminate HU.
Qed.

Lemma closed_value_any_kappa :
  forall v U k k',
    core_value v ->
    core_has_type empty_ctx k v U row_empty k ->
    core_has_type empty_ctx k' v U row_empty k'.
Proof.
  intros v U k k' Hv Htyp.
  inversion Htyp; subst; inversion Hv; subst; constructor.
Qed.

Theorem core_substitution :
  forall Gamma k x U v e T eps k',
    core_value v ->
    core_has_type empty_ctx k v U row_empty k ->
    core_has_type (ctx_extend Gamma x U) k e T eps k' ->
    core_has_type Gamma k (core_subst x v e) T eps k'.
Proof.
  intros Gamma k x U v e T eps k' Hv Hvt Hte.
  remember (ctx_extend Gamma x U) as G eqn:HG.
  generalize dependent Gamma.
  induction Hte; intros Delta HG; subst; simpl.
  - destruct (String.eqb_spec x x0).
    + subst.
      rewrite ctx_extend_eq in H.
      inversion H; subst.
      apply empty_typed_any_context with (Delta := Delta) in Hvt.
      exact Hvt.
    + apply CT_Var.
      rewrite ctx_extend_neq in H by congruence.
      exact H.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - apply CT_LetI with (T1 := T1) (eps1 := eps1) (k1 := k1).
    + eapply IHHte1; eauto.
    + destruct (String.eqb_spec x x0) as [Heq | Hneq].
      * subst x0.
        eapply context_invariance.
        -- exact Hte2.
        -- intros z _.
           rewrite !ctx_extend_shadow.
           reflexivity.
      * eapply (IHHte2 (@closed_value_any_kappa v U k k1 Hv Hvt)
                       (ctx_extend Delta x0 T1)).
        extensionality z.
        unfold ctx_extend.
        destruct (String.eqb_spec x0 z) as [-> | Hz0];
          destruct (String.eqb_spec x z) as [-> | Hz];
          try congruence; reflexivity.
  - constructor.
  - econstructor. exact H.
  - constructor.
  - apply CT_CommitI with (T := T) (omega := omega) (eps := eps).
    eapply IHHte; eauto.
  - apply CT_ReleaseI with (T := T) (omega := omega) (eps := eps).
    eapply IHHte; eauto.
Qed.

Theorem core_effect_row_monotonicity :
  forall Gamma k e T eps k',
    core_has_type Gamma k e T eps k' ->
    row_subsumed (body_row e) eps.
Proof.
  intros Gamma k e T eps k' Htyp.
  induction Htyp.
  - apply row_subsumed_refl.
  - apply row_subsumed_refl.
  - apply row_subsumed_refl.
  - apply row_subsumed_refl.
  - apply row_subsumed_refl.
  - apply row_subsumed_refl.
  - simpl.
    eapply row_subsumed_trans.
    + apply row_subsumed_join_mono; eauto.
    + apply row_subsumed_refl.
  - simpl. apply row_subsumed_refl.
  - simpl. apply row_subsumed_refl.
  - simpl. apply row_subsumed_refl.
  - simpl. apply row_subsumed_refl.
  - simpl. apply row_subsumed_refl.
Qed.

Theorem core_compliance_context_monotonicity :
  forall c c',
    core_step c c' ->
    compliance_le (cfg_kappa c') (cfg_kappa c).
Proof.
  intros c c' Hstep.
  destruct Hstep; simpl; try exact I; destruct k; exact I.
Qed.

Lemma count_occ_remove_same :
  forall x l,
    count_occ String.string_dec (remove_one x l) x =
    Nat.pred (count_occ String.string_dec l x).
Proof.
  intros x l.
  induction l as [| a l IH]; simpl.
  - reflexivity.
  - destruct (String.string_dec x a) as [<- | Hneq].
    + destruct (String.string_dec x x); [simpl; reflexivity | contradiction].
    + destruct (String.string_dec x a); [contradiction |].
      destruct (String.string_dec a x) as [Heq | Hax].
      * exfalso. apply Hneq. symmetry. exact Heq.
      * simpl. destruct (String.string_dec a x); [contradiction | exact IH].
Qed.

Lemma length_remove_once :
  forall x l,
    In x l ->
    S (List.length (remove_one x l)) = List.length l.
Proof.
  intros x l.
  induction l as [| a l IH]; intros Hin.
  - inversion Hin.
  - simpl.
    destruct (String.string_dec x a) as [<- | Hneq].
    + reflexivity.
    + simpl. f_equal. apply IH.
      destruct Hin as [Hin | Hin].
      * subst. contradiction.
      * exact Hin.
Qed.

Definition lock_count (omega : string) (c : core_config) : nat :=
  count_occ String.string_dec (cfg_locked c) omega.

Theorem locked_typestate_single_use :
  forall c c' T omega eps,
    (cfg_expr c = CE_Commit (CE_Locked T omega eps) \/
     cfg_expr c = CE_Release (CE_Locked T omega eps)) ->
    lock_count omega c = 1 ->
    core_step c c' ->
    lock_count omega c' = 0.
Proof.
  intros [e k locks] c' T omega eps Hexpreq Hcount Hstep; simpl in *.
  destruct Hexpreq as [Hexpreq | Hexpreq]; subst e.
  - inversion Hstep; subst; try congruence.
    unfold lock_count in *; simpl in *.
    rewrite count_occ_remove_same.
    rewrite Hcount. reflexivity.
  - inversion Hstep; subst; try congruence.
    unfold lock_count in *; simpl in *.
    rewrite count_occ_remove_same.
    rewrite Hcount. reflexivity.
Qed.

Definition verdict_rank (v : core_verdict) : nat :=
  match v with
  | CV_SanctionsBlocked => 0
  | CV_Review => 1
  | CV_Compliant => 2
  end.

Definition verdict_le (v1 v2 : core_verdict) : Prop :=
  verdict_rank v1 <= verdict_rank v2.

Definition verdict_join (v1 v2 : core_verdict) : core_verdict :=
  match v1, v2 with
  | CV_SanctionsBlocked, _ => CV_SanctionsBlocked
  | _, CV_SanctionsBlocked => CV_SanctionsBlocked
  | CV_Review, _ => CV_Review
  | _, CV_Review => CV_Review
  | CV_Compliant, CV_Compliant => CV_Compliant
  end.

Theorem sanctions_absorption_monotonicity :
  forall v1 v2,
    verdict_le v1 v2 ->
    verdict_join CV_SanctionsBlocked v1 = CV_SanctionsBlocked /\
    verdict_join v1 CV_SanctionsBlocked = CV_SanctionsBlocked /\
    verdict_le
      (verdict_join CV_SanctionsBlocked v1)
      (verdict_join CV_SanctionsBlocked v2).
Proof.
  intros v1 v2 _.
  split.
  - reflexivity.
  - split.
    + destruct v1; reflexivity.
    + unfold verdict_le. simpl. apply le_n.
Qed.

Definition linear_resources (c : core_config) : nat :=
  List.length (cfg_locked c).

Definition consumed_resources (c c' : core_config) : nat :=
  linear_resources c - linear_resources c'.

Theorem linear_resource_conservation :
  forall c c',
    core_step c c' ->
    linear_resources c = linear_resources c' + consumed_resources c c' /\
    linear_resources c' <= linear_resources c.
Proof.
  intros [e k locks] [e' k' locks'] Hstep; simpl in *.
  inversion Hstep; subst; unfold consumed_resources, linear_resources in *; simpl in *.
  - split.
    + rewrite Nat.sub_diag. lia.
    + lia.
  - split.
    + rewrite Nat.sub_diag. lia.
    + lia.
  - split.
    + rewrite Nat.sub_diag. lia.
    + lia.
  - split.
    + pose proof (length_remove_once omega locks H0) as Hlen.
      lia.
    + pose proof (length_remove_once omega locks H0) as Hlen.
      lia.
  - split.
    + pose proof (length_remove_once omega locks H0) as Hlen.
      lia.
    + pose proof (length_remove_once omega locks H0) as Hlen.
      lia.
Qed.

(** ** Full admissible verdict-preservation wrapper. *)

Inductive admissible_lex : Type :=
  | AL_Const : LexValue -> admissible_lex
  | AL_Sanctions : LexValue -> admissible_lex
  | AL_Var : string -> admissible_lex
  | AL_Record : list (string * LexValue) -> admissible_lex
  | AL_List : list LexValue -> admissible_lex
  | AL_Variant : string -> LexValue -> admissible_lex
  | AL_Match : LexValue -> list (LexValue * LexValue) -> admissible_lex
  | AL_Defeasible :
      LexValue ->
      list (nat * nat * bool * LexValue) ->
      admissible_lex
  | AL_Fill : string -> LexValue -> FillWitness -> admissible_lex.

Inductive admissible_op : Type :=
  | AO_Const : OpExpr -> admissible_op
  | AO_Sanctions : SanctOpExpr -> admissible_op
  | AO_Var : VarOpExpr -> admissible_op
  | AO_Record : RecOpExpr -> admissible_op
  | AO_List : ListOpExpr -> admissible_op
  | AO_Variant : VarOE -> admissible_op
  | AO_Match : MatchOpExpr -> admissible_op
  | AO_Defeasible : DefOpExpr -> admissible_op
  | AO_Fill : FillOpExpr -> admissible_op.

Inductive admissible_verdict : Type :=
  | AV_Scalar : LexValue -> admissible_verdict
  | AV_Record : list (string * LexValue) -> admissible_verdict
  | AV_List : list LexValue -> admissible_verdict
  | AV_Variant : string * LexValue -> admissible_verdict.

Definition admissible_compile (t : admissible_lex) : admissible_op :=
  match t with
  | AL_Const v =>
      AO_Const (compile (LT_Const v))
  | AL_Sanctions v =>
      AO_Sanctions (sanct_compile (SLT_Sanctions (SLT_Const v)))
  | AL_Var n =>
      AO_Var (var_compile (VLT_Var n))
  | AL_Record fields =>
      AO_Record (rec_compile (RLT_ConstRec fields))
  | AL_List items =>
      AO_List (list_compile (LLT_Const items))
  | AL_Variant tag v =>
      AO_Variant (variant_compile (VLT_ConstVar tag v))
  | AL_Match scrutinee branches =>
      AO_Match (match_compile (MLT_Match scrutinee branches))
  | AL_Defeasible base exceptions =>
      AO_Defeasible (def_compile (DLT_Def base exceptions))
  | AL_Fill hole_id filler witness =>
      AO_Fill (fill_compile (FLT_Fill hole_id filler witness))
  end.

Inductive admissible_lex_verdict :
  admissible_lex -> admissible_verdict -> Prop :=
  | ALV_Const :
      forall v vv,
        lex_verdict (LT_Const v) vv ->
        admissible_lex_verdict (AL_Const v) (AV_Scalar vv)
  | ALV_Sanctions :
      forall v vv,
        sanct_lex_verdict (SLT_Sanctions (SLT_Const v)) vv ->
        admissible_lex_verdict (AL_Sanctions v) (AV_Scalar vv)
  | ALV_Var :
      forall n vv,
        var_lex_verdict (VLT_Var n) vv ->
        admissible_lex_verdict (AL_Var n) (AV_Scalar vv)
  | ALV_Record :
      forall fields vv,
        rec_lex_verdict (RLT_ConstRec fields) vv ->
        admissible_lex_verdict (AL_Record fields) (AV_Record vv)
  | ALV_List :
      forall items vv,
        list_lex_verdict (LLT_Const items) vv ->
        admissible_lex_verdict (AL_List items) (AV_List vv)
  | ALV_Variant :
      forall tag v vv,
        variant_lex_verdict (VLT_ConstVar tag v) vv ->
        admissible_lex_verdict (AL_Variant tag v) (AV_Variant vv)
  | ALV_Match :
      forall scrutinee branches vv,
        match_lex_verdict (MLT_Match scrutinee branches) vv ->
        admissible_lex_verdict (AL_Match scrutinee branches) (AV_Scalar vv)
  | ALV_Defeasible :
      forall base exceptions vv,
        def_lex_verdict (DLT_Def base exceptions) vv ->
        admissible_lex_verdict (AL_Defeasible base exceptions) (AV_Scalar vv)
  | ALV_Fill :
      forall hole_id filler witness vv,
        fill_lex_verdict (FLT_Fill hole_id filler witness) vv ->
        admissible_lex_verdict (AL_Fill hole_id filler witness) (AV_Scalar vv).

Inductive admissible_op_verdict :
  admissible_op -> admissible_verdict -> Prop :=
  | AOV_Const :
      forall e vv,
        op_verdict e vv ->
        admissible_op_verdict (AO_Const e) (AV_Scalar vv)
  | AOV_Sanctions :
      forall e vv,
        sanct_op_verdict e vv ->
        admissible_op_verdict (AO_Sanctions e) (AV_Scalar vv)
  | AOV_Var :
      forall e vv,
        var_op_verdict e vv ->
        admissible_op_verdict (AO_Var e) (AV_Scalar vv)
  | AOV_Record :
      forall e vv,
        rec_op_verdict e vv ->
        admissible_op_verdict (AO_Record e) (AV_Record vv)
  | AOV_List :
      forall e vv,
        list_op_verdict e vv ->
        admissible_op_verdict (AO_List e) (AV_List vv)
  | AOV_Variant :
      forall e vv,
        variant_op_verdict e vv ->
        admissible_op_verdict (AO_Variant e) (AV_Variant vv)
  | AOV_Match :
      forall e vv,
        match_op_verdict e vv ->
        admissible_op_verdict (AO_Match e) (AV_Scalar vv)
  | AOV_Defeasible :
      forall e vv,
        def_op_verdict e vv ->
        admissible_op_verdict (AO_Defeasible e) (AV_Scalar vv)
  | AOV_Fill :
      forall e vv,
        fill_op_weak_verdict e vv ->
        admissible_op_verdict (AO_Fill e) (AV_Scalar vv).

Theorem verdict_preservation_admissible :
  forall t vv,
    admissible_lex_verdict t vv <->
    admissible_op_verdict (admissible_compile t) vv.
Proof.
  intros t vv.
  destruct t; split; intro H.
  - inversion H; subst.
    apply AOV_Const.
    now apply verdict_preservation_const.
  - inversion H; subst.
    apply ALV_Const.
    now apply verdict_preservation_const.
  - inversion H; subst.
    apply AOV_Sanctions.
    now apply verdict_preservation_sanctions.
  - inversion H; subst.
    apply ALV_Sanctions.
    now apply verdict_preservation_sanctions.
  - inversion H; subst.
    apply AOV_Var.
    now apply verdict_preservation_var.
  - inversion H; subst.
    apply ALV_Var.
    now apply verdict_preservation_var.
  - inversion H; subst.
    apply AOV_Record.
    now apply verdict_preservation_const_record.
  - inversion H; subst.
    apply ALV_Record.
    now apply verdict_preservation_const_record.
  - inversion H; subst.
    apply AOV_List.
    now apply verdict_preservation_const_list.
  - inversion H; subst.
    apply ALV_List.
    now apply verdict_preservation_const_list.
  - inversion H; subst.
    apply AOV_Variant.
    now apply verdict_preservation_const_variant.
  - inversion H; subst.
    apply ALV_Variant.
    now apply verdict_preservation_const_variant.
  - inversion H; subst.
    apply AOV_Match.
    now apply verdict_preservation_match.
  - inversion H; subst.
    apply ALV_Match.
    now apply verdict_preservation_match.
  - inversion H; subst.
    apply AOV_Defeasible.
    now apply verdict_preservation_defeasible.
  - inversion H; subst.
    apply ALV_Defeasible.
    now apply verdict_preservation_defeasible.
  - inversion H; subst.
    apply AOV_Fill.
    now apply verdict_preservation_fill.
  - inversion H; subst.
    apply ALV_Fill.
    now apply verdict_preservation_fill.
Qed.
