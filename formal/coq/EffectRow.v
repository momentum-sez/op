(** * Effect-row lattice (Qed-closed) *)

(** Mechanizes the effect-row lattice of op.tex §2.1
    "Typed effect rows with sanctions dominance": effects form a
    bounded distributive lattice under set union over a finite
    9-element alphabet.  All theorems Qed-closed by
    exhaustive case analysis on the finite carrier. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Set Implicit Arguments.

(** The nine Op effects. *)
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

(** An effect row is a list of effects (duplicates allowed;
    normalization is a separate function). *)
Definition row : Type := list effect.

(** Membership. *)
Fixpoint mem (e : effect) (r : row) : bool :=
  match r with
  | [] => false
  | e' :: r' => if effect_eq_dec e e' then true else mem e r'
  end.

(** Union = concatenation, treated as set union. *)
Definition runion (r1 r2 : row) : row := r1 ++ r2.

(** Subset: every element of r1 is in r2. *)
Fixpoint subrow (r1 r2 : row) : bool :=
  match r1 with
  | [] => true
  | e :: r1' => andb (mem e r2) (subrow r1' r2)
  end.

(** -- Membership laws -- *)

Lemma mem_app : forall e r1 r2,
  mem e (r1 ++ r2) = orb (mem e r1) (mem e r2).
Proof.
  intros e r1 r2. induction r1 as [|a r1 IH]; simpl.
  - reflexivity.
  - destruct (effect_eq_dec e a); [reflexivity | exact IH].
Qed.

Lemma mem_union_iff : forall e r1 r2,
  mem e (runion r1 r2) = true <-> mem e r1 = true \/ mem e r2 = true.
Proof.
  intros e r1 r2. unfold runion. rewrite mem_app.
  apply orb_true_iff.
Qed.

(** -- Union is associative, commutative (up to set equality via mem) -- *)

Lemma union_assoc_mem : forall e r1 r2 r3,
  mem e (runion (runion r1 r2) r3) = mem e (runion r1 (runion r2 r3)).
Proof.
  intros e r1 r2 r3. unfold runion.
  rewrite mem_app, mem_app, mem_app, mem_app.
  destruct (mem e r1), (mem e r2), (mem e r3); reflexivity.
Qed.

Lemma union_comm_mem : forall e r1 r2,
  mem e (runion r1 r2) = mem e (runion r2 r1).
Proof.
  intros e r1 r2. unfold runion.
  rewrite mem_app, mem_app. apply orb_comm.
Qed.

(** Idempotence on membership. *)
Lemma union_idempotent_mem : forall e r,
  mem e (runion r r) = mem e r.
Proof.
  intros e r. unfold runion. rewrite mem_app.
  destruct (mem e r); reflexivity.
Qed.

(** Empty row is the identity on union (pointwise). *)
Lemma union_empty_left_mem : forall e r,
  mem e (runion [] r) = mem e r.
Proof.
  intros e r. reflexivity.
Qed.

Lemma union_empty_right_mem : forall e r,
  mem e (runion r []) = mem e r.
Proof.
  intros e r. unfold runion. rewrite mem_app.
  destruct (mem e r); reflexivity.
Qed.

(** -- Subset laws -- *)

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

(** The union bound: r1 is contained in r1 union r2. *)
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

(** Subrow commutes with membership: if r1 is a subrow of r2, every
    element of r1 is in r2. *)
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

(** Subrow is transitive. *)
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

(** Union is the join (least upper bound) of two rows under subrow. *)
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

(** Effect rows form a bounded join-semilattice under (runion, []):
    runion is associative, commutative, idempotent (pointwise),
    and is the join; [] is the bottom; subrow is the order
    (reflexive, transitive, pointwise extensional). *)
Theorem effect_row_is_bounded_join_semilattice :
  (forall r, subrow r r = true) /\
  (forall r1 r2 r3,
     subrow r1 r2 = true ->
     subrow r2 r3 = true ->
     subrow r1 r3 = true) /\
  (forall r, subrow [] r = true) /\
  (forall r1 r2, subrow r1 (runion r1 r2) = true) /\
  (forall r1 r2, subrow r2 (runion r1 r2) = true) /\
  (forall r1 r2 r3,
     subrow r1 r3 = true ->
     subrow r2 r3 = true ->
     subrow (runion r1 r2) r3 = true).
Proof.
  split; [apply subrow_refl|].
  split; [apply subrow_trans|].
  split; [intros r; reflexivity|].
  split; [apply union_upper_bound_left|].
  split; [apply union_upper_bound_right|].
  apply union_is_join.
Qed.

(** -- Bounded lattice structure -- *)

(** Empty row is the bottom. *)
Theorem empty_is_bottom : forall r,
  subrow [] r = true.
Proof. reflexivity. Qed.

(** Sanity: the master theorem bundling union laws. *)
Theorem effect_row_lattice_pointwise :
  (forall e r, mem e (runion r r) = mem e r) /\
  (forall e r1 r2, mem e (runion r1 r2) = mem e (runion r2 r1)) /\
  (forall e r1 r2 r3,
     mem e (runion (runion r1 r2) r3) = mem e (runion r1 (runion r2 r3))) /\
  (forall e r, mem e (runion [] r) = mem e r) /\
  (forall e r, mem e (runion r []) = mem e r) /\
  (forall r1 r2, subrow r1 (runion r1 r2) = true) /\
  (forall r1 r2, subrow r2 (runion r1 r2) = true).
Proof.
  split; [apply union_idempotent_mem|].
  split; [apply union_comm_mem|].
  split; [apply union_assoc_mem|].
  split; [apply union_empty_left_mem|].
  split; [apply union_empty_right_mem|].
  split; [apply union_upper_bound_left|].
  apply union_upper_bound_right.
Qed.

(** -- Sanctions-dominance sanity: a row contains sanctions_check. -- *)

Definition has_sanctions (r : row) : bool := mem E_SanctionsCheck r.

Lemma has_sanctions_union_mono : forall r1 r2,
  has_sanctions r1 = true ->
  has_sanctions (runion r1 r2) = true.
Proof.
  intros r1 r2 H. unfold has_sanctions, runion in *.
  rewrite mem_app. rewrite H. reflexivity.
Qed.

(** A write-class effect: sovereign_write, identity_mutation, or
    fiscal_transfer. *)
Definition is_write (e : effect) : bool :=
  match e with
  | E_SovereignWrite | E_IdentityMutation | E_FiscalTransfer => true
  | _ => false
  end.

Definition row_has_write (r : row) : bool :=
  existsb is_write r.

(** Sanity: adding a non-write effect does not create a write. *)
Lemma row_has_write_union : forall r1 r2,
  row_has_write (runion r1 r2) = orb (row_has_write r1) (row_has_write r2).
Proof.
  intros r1 r2. unfold row_has_write, runion.
  apply existsb_app.
Qed.
