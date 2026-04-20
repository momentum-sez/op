(** * Proof-bundle append-only invariant (Qed-closed) *)

(** Mechanizes the append-only bundle invariant (BSC invariant
    I1) of op.tex §2.2 and §5: the proof bundle grows
    monotonically along any reduction sequence; no step ever
    removes or replaces an existing bundle entry.  Abstracted
    here as a pure list-prefix claim parameterized over an
    arbitrary entry type.  All theorems Qed-closed. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Set Implicit Arguments.

(** Abstract proof-bundle semantics: a reduction step preserves
    the prefix structure of the bundle. *)
Module Type AppendOnlyBundle.
  Parameter conf : Type.
  Parameter entry : Type.
  Parameter step : conf -> conf -> Prop.
  Parameter bundle : conf -> list entry.

  (** Single-step append-only: after a step, the new bundle is an
      extension of the old bundle (possibly the same, possibly
      with one or more new entries appended). *)
  Axiom bundle_step_prefix :
    forall c c', step c c' ->
      exists ext, bundle c' = bundle c ++ ext.
End AppendOnlyBundle.

Module BundleMonotonicity (B : AppendOnlyBundle).

  (** Multi-step closure. *)
  Inductive multi_step : B.conf -> B.conf -> Prop :=
    | multi_step_refl : forall c, multi_step c c
    | multi_step_cons : forall c c' c'',
        B.step c c' -> multi_step c' c'' -> multi_step c c''.

  (** Bundle monotonicity across any reduction trace. *)
  Theorem bundle_multi_step_prefix :
    forall c c', multi_step c c' ->
      exists ext, B.bundle c' = B.bundle c ++ ext.
  Proof.
    intros c c' H. induction H.
    - exists []. rewrite app_nil_r. reflexivity.
    - destruct (B.bundle_step_prefix H) as [ext1 Heq1].
      destruct IHmulti_step as [ext2 Heq2].
      exists (ext1 ++ ext2).
      rewrite Heq2. rewrite Heq1.
      rewrite app_assoc. reflexivity.
  Qed.

  (** Corollary: bundle length is monotone non-decreasing across
      any reduction trace. *)
  Theorem bundle_length_monotone :
    forall c c', multi_step c c' ->
      length (B.bundle c) <= length (B.bundle c').
  Proof.
    intros c c' H.
    destruct (bundle_multi_step_prefix H) as [ext Heq].
    rewrite Heq, app_length.
    apply Nat.le_add_r.
  Qed.

  (** Corollary: every position in the old bundle retains the
      same entry in the new bundle (no mutation of prior
      entries).  Formalized as: the [nth_error] of the old
      bundle at position [i] equals the [nth_error] of the new
      bundle at the same position. *)
  Theorem bundle_entries_preserved :
    forall c c' i,
      multi_step c c' ->
      i < length (B.bundle c) ->
      nth_error (B.bundle c) i = nth_error (B.bundle c') i.
  Proof.
    intros c c' i H Hlen.
    destruct (bundle_multi_step_prefix H) as [ext Heq].
    rewrite Heq.
    (** [nth_error (xs ++ ys) i = nth_error xs i] when [i < length xs]. *)
    clear - Hlen. generalize dependent i.
    induction (B.bundle c) as [|e bs IH]; intros i Hlen; simpl in *.
    - lia.
    - destruct i as [|i']; [reflexivity|].
      apply IH. lia.
  Qed.

  (** Transitivity of multi_step. *)
  Lemma multi_step_trans :
    forall c c' c'',
      multi_step c c' -> multi_step c' c'' -> multi_step c c''.
  Proof.
    intros c c' c'' H1 H2. induction H1.
    - exact H2.
    - eapply multi_step_cons. eexact H. apply IHmulti_step. exact H2.
  Qed.

  (** A bundle entry, once present, remains present forever. *)
  Theorem bundle_entry_persistence :
    forall c c' i e,
      multi_step c c' ->
      nth_error (B.bundle c) i = Some e ->
      nth_error (B.bundle c') i = Some e.
  Proof.
    intros c c' i e H Hnth.
    assert (Hlen : i < length (B.bundle c)).
    { apply nth_error_Some.
      rewrite Hnth. intro Hcon. discriminate. }
    rewrite <- (bundle_entries_preserved H Hlen). exact Hnth.
  Qed.

  (** The bundle-length function is a monotone map from conf to
      nat under multi_step.  Sanity: no step ever shrinks the
      bundle. *)
  Corollary bundle_length_never_decreases :
    forall c c',
      multi_step c c' ->
      length (B.bundle c') >= length (B.bundle c).
  Proof.
    intros c c' H. apply bundle_length_monotone. exact H.
  Qed.

End BundleMonotonicity.
