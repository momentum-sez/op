(** * Corridor-history monotonicity for Op BSC typing *)

(** This file states the corridor-history monotonicity lemma of
    [Op] paper lem:kappa-monotone as a Rocq development.  The lemma
    is the preservation witness for the SJN invariants (I1)-(I3) by
    typing: every BSC typing rule (T-Lock, T-Sign, T-Verify, T-Blame,
    T-Lock-Timeout) extends kappa additively, never weakening any
    cell. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Set Implicit Arguments.

(** A corridor-history coordinate names a side X (Initiator or
    Responder), an operation index omega, and an epoch index epsilon,
    plus a kind discriminating the four cell families. *)
Inductive side : Type := Initiator | Responder.

Inductive coord_kind : Type :=
  | ActiveLock      (** active_lock_X(omega, epsilon) := deadline *)
  | HistoryOf       (** history_of_X(omega, epsilon) := digest *)
  | Verified        (** verified_X(omega, epsilon)   := {s_A, s_B} *)
  | Blame.          (** blame_X(omega, epsilon, Z)   := {s_1, s_2} *)

Definition coord : Type := side * coord_kind * nat * nat.

(** Corridor history is a finite partial map from coord to a
    polymorphic value type.  We model it as an association list
    with the convention that earlier entries shadow later ones
    (equivalent to a finite map). *)
Definition kappa (V : Type) : Type := list (coord * V).

(** Decidable equality on coord built up from components. *)
Lemma side_eq_dec : forall s1 s2 : side, {s1 = s2} + {s1 <> s2}.
Proof. decide equality. Defined.

Lemma coord_kind_eq_dec : forall k1 k2 : coord_kind, {k1 = k2} + {k1 <> k2}.
Proof. decide equality. Defined.

Lemma coord_eq_dec : forall c1 c2 : coord, {c1 = c2} + {c1 <> c2}.
Proof.
  intros [[[s1 k1] o1] e1] [[[s2 k2] o2] e2].
  destruct (side_eq_dec s1 s2); [| right; congruence].
  destruct (coord_kind_eq_dec k1 k2); [| right; congruence].
  destruct (Nat.eq_dec o1 o2); [| right; congruence].
  destruct (Nat.eq_dec e1 e2); [| right; congruence].
  subst. left. reflexivity.
Defined.

(** Lookup. *)
Fixpoint lookup {V : Type} (k : kappa V) (c : coord) : option V :=
  match k with
  | nil => None
  | (c', v) :: k' =>
      if coord_eq_dec c c' then Some v else lookup k' c
  end.

(** Subset order: kappa1 sqsubseteq kappa2 iff every cell in
    kappa1 is also in kappa2 with the same value. *)
Definition kappa_sub {V : Type} (k1 k2 : kappa V) : Prop :=
  forall c v, lookup k1 c = Some v -> lookup k2 c = Some v.

(** Reflexivity. *)
Lemma kappa_sub_refl : forall V (k : kappa V), kappa_sub k k.
Proof.
  intros V k c v H. exact H.
Qed.

(** Transitivity. *)
Lemma kappa_sub_trans : forall V (k1 k2 k3 : kappa V),
  kappa_sub k1 k2 -> kappa_sub k2 k3 -> kappa_sub k1 k3.
Proof.
  intros V k1 k2 k3 H12 H23 c v H1.
  apply H23. apply H12. exact H1.
Qed.

(** Additive extension: cons preserves and extends sub. *)
Lemma kappa_sub_cons :
  forall V (k : kappa V) c v,
    lookup k c = None ->
    kappa_sub k ((c, v) :: k).
Proof.
  intros V k c v Hnone c' v' Hlk.
  simpl. destruct (coord_eq_dec c' c) as [Heq | Hneq].
  - subst c'. rewrite Hnone in Hlk. discriminate.
  - exact Hlk.
Qed.

(** A typing-rule output extension: every rule emits a fresh cell. *)
Definition extends_with {V : Type} (k k' : kappa V) (c : coord) (v : V) : Prop :=
  k' = (c, v) :: k /\ lookup k c = None.

Lemma extends_with_implies_sub :
  forall V (k k' : kappa V) c v,
    extends_with k k' c v -> kappa_sub k k'.
Proof.
  intros V k k' c v [Hk' Hnone]. subst k'.
  apply kappa_sub_cons. exact Hnone.
Qed.

(** ** Additional kappa_sub properties *)

(** The empty kappa is a subset of every kappa. *)
Lemma kappa_sub_empty : forall V (k : kappa V),
  kappa_sub (@nil (coord * V)) k.
Proof.
  intros V k c v H. simpl in H. discriminate.
Qed.

(** If [k1 ⊑ k2], then prepending the same cell on both preserves
    the sub relation (provided the new coord is fresh in both). *)
Lemma kappa_sub_cons_cong :
  forall V (k1 k2 : kappa V) c v,
    kappa_sub k1 k2 ->
    kappa_sub ((c, v) :: k1) ((c, v) :: k2).
Proof.
  intros V k1 k2 c v Hsub c' v' Hlk.
  simpl in *.
  destruct (coord_eq_dec c' c) as [Heq | Hneq].
  - exact Hlk.
  - apply Hsub. exact Hlk.
Qed.

(** An extended kappa contains the extension cell. *)
Lemma extends_with_contains_cell :
  forall V (k k' : kappa V) c v,
    extends_with k k' c v ->
    lookup k' c = Some v.
Proof.
  intros V k k' c v [Hk' Hnone]. subst k'. simpl.
  destruct (coord_eq_dec c c) as [_ | Hne]; [reflexivity | contradiction].
Qed.

(** Two consecutive extensions yield a sub chain from the initial
    kappa to the final kappa. *)
Lemma extends_with_chain_implies_sub :
  forall V (k1 k2 k3 : kappa V) c2 v2 c3 v3,
    extends_with k1 k2 c2 v2 ->
    extends_with k2 k3 c3 v3 ->
    kappa_sub k1 k3.
Proof.
  intros V k1 k2 k3 c2 v2 c3 v3 H12 H23.
  apply kappa_sub_trans with (k2 := k2).
  - eapply extends_with_implies_sub. exact H12.
  - eapply extends_with_implies_sub. exact H23.
Qed.

(** If the same coord maps to two different values in two related
    kappas under [kappa_sub], that's impossible: values agree. *)
Lemma kappa_sub_lookup_functional :
  forall V (k1 k2 : kappa V) c v1 v2,
    kappa_sub k1 k2 ->
    lookup k1 c = Some v1 ->
    lookup k2 c = Some v2 ->
    v1 = v2.
Proof.
  intros V k1 k2 c v1 v2 Hsub Hl1 Hl2.
  apply Hsub in Hl1. rewrite Hl1 in Hl2. inversion Hl2. reflexivity.
Qed.

(** The corridor-history monotonicity lemma, stated abstractly:
    every typing-rule reduction extends kappa.  The actual rule
    inductive (T-Lock, T-Sign, T-Verify, T-Blame, T-Lock-Timeout)
    is parameterized; the user supplies the per-rule extension
    proofs. *)
(** ** Additional lookup / extension structural lemmas (2026-04-20) *)

(** Lookup on the empty kappa is always [None]. *)
Lemma lookup_nil : forall V c, lookup (@nil (coord * V)) c = None.
Proof. reflexivity. Qed.

(** Lookup on a cons whose head matches returns [Some v]. *)
Lemma lookup_cons_match :
  forall V (k : kappa V) c v, lookup ((c, v) :: k) c = Some v.
Proof.
  intros V k c v. simpl.
  destruct (coord_eq_dec c c) as [_|Hne]; [reflexivity | contradiction].
Qed.

(** Lookup on a cons whose head does not match recurses. *)
Lemma lookup_cons_nomatch :
  forall V (k : kappa V) c c' v,
    c <> c' -> lookup ((c', v) :: k) c = lookup k c.
Proof.
  intros V k c c' v Hne. simpl.
  destruct (coord_eq_dec c c') as [Heq|_]; [contradiction | reflexivity].
Qed.

(** An extension preserves old entries: if [lookup k c = Some v], the
    extension [(c', v') :: k] also returns [Some v] at [c] (assuming
    [c <> c']). *)
Lemma extension_preserves_lookup :
  forall V (k : kappa V) c c' v v',
    c <> c' ->
    lookup k c = Some v ->
    lookup ((c', v') :: k) c = Some v.
Proof.
  intros V k c c' v v' Hne Hl.
  rewrite lookup_cons_nomatch; [exact Hl | exact Hne].
Qed.

(** If [c] has [None] in both k1 and k2, and kappa_sub holds, then
    the [None] is preserved. *)
Lemma kappa_sub_preserves_absent :
  forall V (k1 k2 : kappa V) c,
    kappa_sub k1 k2 ->
    lookup k1 c = None ->
    (forall v, lookup k1 c <> Some v).
Proof.
  intros V k1 k2 c _ Hnone v Hsome. rewrite Hnone in Hsome. discriminate.
Qed.

Module Type RuleExtension.
  Parameter V : Type.
  Parameter rule_step : kappa V -> kappa V -> Prop.

  Axiom rule_step_extends :
    forall k k', rule_step k k' ->
      k = k' \/ exists c v, extends_with k k' c v.
End RuleExtension.

Module CorridorMonotone (R : RuleExtension).

  Theorem kappa_monotone :
    forall k k', R.rule_step k k' -> kappa_sub k k'.
  Proof.
    intros k k' H.
    pose proof (R.rule_step_extends H) as Hext_or.
    destruct Hext_or as [Heq | [c [v Hext]]].
    - subst k'. apply kappa_sub_refl.
    - eapply extends_with_implies_sub. exact Hext.
  Qed.

End CorridorMonotone.
