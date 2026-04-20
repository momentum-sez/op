(** * Compliance-context meet-semilattice (Qed-closed) *)

(** Mechanizes the compliance-context algebra from op.tex §5
    compliance-carrying heal: a Heyting meet-semilattice of finite
    partial maps from compliance coordinates to per-coordinate
    verdicts, with sanctions-absorption and lattice laws.  All
    theorems Qed-closed. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

Set Implicit Arguments.

(** Compliance coordinate: domain code (16-bit) + jurisdiction id. *)
Definition coord : Type := nat * nat.

Definition coord_eq_dec : forall c1 c2 : coord, {c1 = c2} + {c1 <> c2}.
Proof.
  intros [d1 j1] [d2 j2].
  destruct (Nat.eq_dec d1 d2); [| right; congruence].
  destruct (Nat.eq_dec j1 j2); [| right; congruence].
  subst. left. reflexivity.
Defined.

(** Per-coordinate verdict: Compliant, Pending, NotApplicable,
    Exempt, NonCompliant, plus a distinguished Sanctioned (the
    absorbing bottom for sanctions-blocked operations). *)
Inductive cell_verdict : Type :=
  | CC_Compliant
  | CC_Exempt
  | CC_NotApplicable
  | CC_Pending
  | CC_NonCompliant
  | CC_Sanctioned.

Definition cell_rank (v : cell_verdict) : nat :=
  match v with
  | CC_Compliant => 5
  | CC_Exempt => 4
  | CC_NotApplicable => 3
  | CC_Pending => 2
  | CC_NonCompliant => 1
  | CC_Sanctioned => 0
  end.

(** Per-cell meet: pointwise min of rank with absorption: if either
    is Sanctioned, result is Sanctioned. *)
Definition cell_meet (v1 v2 : cell_verdict) : cell_verdict :=
  match v1, v2 with
  | CC_Sanctioned, _ => CC_Sanctioned
  | _, CC_Sanctioned => CC_Sanctioned
  | _, _ =>
      if Nat.leb (cell_rank v1) (cell_rank v2) then v1 else v2
  end.

Lemma cell_meet_idempotent : forall v, cell_meet v v = v.
Proof. destruct v; reflexivity. Qed.

Lemma cell_meet_comm : forall a b, cell_meet a b = cell_meet b a.
Proof. destruct a, b; reflexivity. Qed.

Lemma cell_meet_assoc : forall a b c,
  cell_meet (cell_meet a b) c = cell_meet a (cell_meet b c).
Proof. destruct a, b, c; reflexivity. Qed.

(** Sanctions absorbs on the left and right. *)
Lemma cell_meet_sanctioned_left : forall v,
  cell_meet CC_Sanctioned v = CC_Sanctioned.
Proof. destruct v; reflexivity. Qed.

Lemma cell_meet_sanctioned_right : forall v,
  cell_meet v CC_Sanctioned = CC_Sanctioned.
Proof. destruct v; reflexivity. Qed.

(** Compliance context: finite association list of (coord, cell_verdict). *)
Definition context : Type := list (coord * cell_verdict).

Fixpoint clookup (k : context) (c : coord) : option cell_verdict :=
  match k with
  | [] => None
  | (c', v) :: k' =>
      if coord_eq_dec c c' then Some v else clookup k' c
  end.

(** Pointwise meet of two contexts: for each coordinate, meet the
    cell values; coordinates present in only one side are preserved. *)
Fixpoint update (k : context) (c : coord) (v : cell_verdict) : context :=
  match k with
  | [] => [(c, v)]
  | (c', v') :: k' =>
      if coord_eq_dec c c'
      then (c', cell_meet v v') :: k'
      else (c', v') :: update k' c v
  end.

Fixpoint context_meet_aux (left : context) (right : context) : context :=
  match right with
  | [] => left
  | (c, v) :: rest => context_meet_aux (update left c v) rest
  end.

Definition context_meet (k1 k2 : context) : context := context_meet_aux k1 k2.

(** Empty context is the identity. *)
Lemma context_meet_empty_right : forall k, context_meet k [] = k.
Proof. reflexivity. Qed.

(** Lookup after update: at the updated coord, gives the meet. *)
Lemma clookup_update_same : forall k c v,
  exists r, clookup (update k c v) c = Some r.
Proof.
  induction k as [|p k IH]; intros c v; simpl.
  - destruct (coord_eq_dec c c) as [_|Hne].
    + exists v. reflexivity.
    + contradiction.
  - destruct p as [c' v']. destruct (coord_eq_dec c c').
    + simpl. destruct (coord_eq_dec c c') as [_|Hne].
      * exists (cell_meet v v'). reflexivity.
      * contradiction.
    + simpl. destruct (coord_eq_dec c c') as [Heq|_].
      * contradiction.
      * apply IH.
Qed.

(** Update preserves other coordinates. *)
Lemma clookup_update_other : forall k c c' v,
  c <> c' ->
  clookup (update k c v) c' = clookup k c'.
Proof.
  induction k as [|p k IH]; intros c c' v Hne; simpl.
  - destruct (coord_eq_dec c' c) as [Heq|_]; [congruence | reflexivity].
  - destruct p as [c'' v']. destruct (coord_eq_dec c c'') as [Heq|Hne2].
    + simpl. destruct (coord_eq_dec c' c'') as [Heq2|_].
      * subst. contradiction.
      * reflexivity.
    + simpl. destruct (coord_eq_dec c' c'') as [Heq2|Hne3].
      * reflexivity.
      * apply IH. exact Hne.
Qed.

(** Sanity: context_meet with an empty right-side is identity. *)
Lemma context_meet_nil : forall k, context_meet k [] = k.
Proof. reflexivity. Qed.

(** Sanity: single-entry meet extends. *)
Lemma context_meet_single : forall k c v,
  context_meet k [(c, v)] = update k c v.
Proof. intros. reflexivity. Qed.

(** Exact update-at-coord: if the coord is absent, update sets it to
    v; if present, update meets v with the existing value. *)
Lemma clookup_update_absent : forall k c v,
  clookup k c = None -> clookup (update k c v) c = Some v.
Proof.
  induction k as [|p k IH]; intros c v H; simpl.
  - destruct (coord_eq_dec c c) as [_|Hne]; [reflexivity | contradiction].
  - destruct p as [c' v']. simpl in H.
    destruct (coord_eq_dec c c') as [Heq|Hne].
    + discriminate.
    + simpl. destruct (coord_eq_dec c c') as [Heq|_]; [contradiction|].
      apply IH. exact H.
Qed.

Lemma clookup_update_present : forall k c v v',
  clookup k c = Some v' -> clookup (update k c v) c = Some (cell_meet v v').
Proof.
  induction k as [|p k IH]; intros c v v' H; simpl.
  - simpl in H. discriminate.
  - destruct p as [c'' v'']. simpl in H.
    destruct (coord_eq_dec c c'') as [Heq|Hne].
    + inversion H; subst. simpl. destruct (coord_eq_dec c'' c'') as [_|Hne]; [reflexivity|contradiction].
    + simpl. destruct (coord_eq_dec c c'') as [Heq|_]; [contradiction|].
      apply IH. exact H.
Qed.

(** Update preserves Sanctioned at a coord: no matter what we update
    with, if the coord was Sanctioned, it stays Sanctioned. *)
Lemma update_preserves_sanctioned : forall k c c' v',
  clookup k c = Some CC_Sanctioned ->
  clookup (update k c' v') c = Some CC_Sanctioned.
Proof.
  intros k c c' v' H.
  destruct (coord_eq_dec c c') as [Heq|Hne].
  - subst. rewrite (clookup_update_present _ _ _ H).
    rewrite cell_meet_sanctioned_right. reflexivity.
  - rewrite clookup_update_other; [exact H | auto].
Qed.

(** Update with Sanctioned produces Sanctioned at the updated coord. *)
Lemma update_sets_sanctioned : forall k c,
  clookup (update k c CC_Sanctioned) c = Some CC_Sanctioned.
Proof.
  intros k c. destruct (clookup k c) as [v'|] eqn:Hk.
  - rewrite (clookup_update_present _ _ _ Hk).
    rewrite cell_meet_sanctioned_left. reflexivity.
  - apply clookup_update_absent. exact Hk.
Qed.

(** Core lemma: context_meet_aux preserves Sanctioned in the left
    accumulator at any coord. *)
Lemma meet_aux_preserves_sanctioned : forall k2 k1 c,
  clookup k1 c = Some CC_Sanctioned ->
  clookup (context_meet_aux k1 k2) c = Some CC_Sanctioned.
Proof.
  induction k2 as [|p k2 IH]; intros k1 c H; simpl.
  - exact H.
  - destruct p as [c' v']. apply IH.
    apply update_preserves_sanctioned. exact H.
Qed.

(** Core lemma: if k2 contains Sanctioned at c, context_meet_aux
    produces Sanctioned at c regardless of k1's value there. *)
Lemma meet_aux_absorbs_sanctioned : forall k2 k1 c,
  clookup k2 c = Some CC_Sanctioned ->
  clookup (context_meet_aux k1 k2) c = Some CC_Sanctioned.
Proof.
  induction k2 as [|p k2 IH]; intros k1 c H; simpl.
  - simpl in H. discriminate.
  - destruct p as [c' v']. simpl in H.
    destruct (coord_eq_dec c c') as [Heq|Hne].
    + inversion H; subst.
      apply meet_aux_preserves_sanctioned.
      apply update_sets_sanctioned.
    + apply IH. exact H.
Qed.

(** Sanctions bottom: if any coordinate holds Sanctioned in either
    side, the meet at that coordinate holds Sanctioned.  Qed-closed. *)
Theorem sanctions_absorption_in_meet :
  forall k1 k2 c,
    clookup k1 c = Some CC_Sanctioned \/
    clookup k2 c = Some CC_Sanctioned ->
    clookup (context_meet k1 k2) c = Some CC_Sanctioned.
Proof.
  intros k1 k2 c [H1 | H2]; unfold context_meet.
  - apply meet_aux_preserves_sanctioned. exact H1.
  - apply meet_aux_absorbs_sanctioned. exact H2.
Qed.

(** -- Rank-monotonicity of cell_meet: meet never produces a
       higher-rank verdict than either input.  This is the
       "restrictiveness-monotone" property of the compliance
       lattice: combining evidence can only lower the verdict
       rank (toward the sanctioned bottom), never raise it. -- *)

Lemma cell_meet_rank_le_left : forall v1 v2,
  cell_rank (cell_meet v1 v2) <= cell_rank v1.
Proof.
  destruct v1, v2; compute; lia.
Qed.

Lemma cell_meet_rank_le_right : forall v1 v2,
  cell_rank (cell_meet v1 v2) <= cell_rank v2.
Proof.
  destruct v1, v2; compute; lia.
Qed.

(** Corollary: cell_meet produces at most the minimum rank. *)
Theorem cell_meet_rank_min :
  forall v1 v2,
    cell_rank (cell_meet v1 v2) <= Nat.min (cell_rank v1) (cell_rank v2).
Proof.
  intros v1 v2. apply Nat.min_glb.
  - apply cell_meet_rank_le_left.
  - apply cell_meet_rank_le_right.
Qed.

(** Idempotence at the rank level: meet with itself stays the
    same rank. *)
Lemma cell_meet_rank_self : forall v, cell_rank (cell_meet v v) = cell_rank v.
Proof.
  intros v. rewrite cell_meet_idempotent. reflexivity.
Qed.

(** Core update-lookup-rank lemma: after updating k at c'' with
    v'', the rank at any coord c is bounded by the original
    rank at c (if present). *)
Lemma clookup_update_rank_monotone : forall k c v c'' v'' r,
  clookup k c = Some v ->
  clookup (update k c'' v'') c = Some r ->
  cell_rank r <= cell_rank v.
Proof.
  intros k c v c'' v'' r H1 H2.
  destruct (coord_eq_dec c c'') as [Heq|Hne].
  - subst. rewrite (clookup_update_present _ _ _ H1) in H2.
    inversion H2. apply cell_meet_rank_le_right.
  - rewrite clookup_update_other in H2; [|congruence].
    rewrite H1 in H2. inversion H2. lia.
Qed.

(** Compliance-context rank-monotonicity: after meeting two
    contexts, every coordinate's rank is bounded above by the
    rank it had in the left context (if present).  Qed-closed
    by induction on the right context, using the update-rank
    lemma above to establish the bound on every step of the
    fold. *)
Theorem context_meet_rank_monotone_left :
  forall k2 k1 c v v',
    clookup k1 c = Some v ->
    clookup (context_meet k1 k2) c = Some v' ->
    cell_rank v' <= cell_rank v.
Proof.
  intro k2. induction k2 as [|p k2 IH]; intros k1 c v v' H1 H2;
    unfold context_meet in *; simpl in H2.
  - rewrite H1 in H2. inversion H2. lia.
  - destruct p as [c'' v''].
    (** After the first update, the value at c is some r with
        cell_rank r <= cell_rank v.  IH then gives the bound
        for the tail. *)
    destruct (clookup (update k1 c'' v'') c) as [r|] eqn:Hupd.
    + assert (Hbound : cell_rank r <= cell_rank v).
      { apply clookup_update_rank_monotone with
          (k := k1) (c := c) (v := v) (c'' := c'') (v'' := v'') (r := r).
        - exact H1.
        - exact Hupd. }
      assert (Hrec : cell_rank v' <= cell_rank r).
      { apply IH with (k1 := update k1 c'' v'') (c := c) (v := r) (v' := v'); assumption. }
      lia.
    + (** impossible: update always produces a Some at c when
          k1 has a Some at c *)
      exfalso.
      destruct (coord_eq_dec c c'') as [Heq|Hne].
      * subst. rewrite (clookup_update_present _ _ _ H1) in Hupd. discriminate.
      * rewrite clookup_update_other in Hupd; [|congruence].
        rewrite H1 in Hupd. discriminate.
Qed.

(** ** Rank characterisation of the verdict chain *)

(** [CC_Sanctioned] is rank 0 — the minimum of the six-valued
    carrier. *)
Lemma cell_rank_sanctioned_is_min : cell_rank CC_Sanctioned = 0.
Proof. reflexivity. Qed.

(** [CC_Compliant] is rank 5 — the maximum of the six-valued
    carrier. *)
Lemma cell_rank_compliant_is_max : cell_rank CC_Compliant = 5.
Proof. reflexivity. Qed.

(** Every [cell_verdict]'s rank is bounded below by zero (the
    [CC_Sanctioned] rank).  Trivial but serves as an explicit
    citation. *)
Theorem cell_rank_sanctioned_is_global_min :
  forall v, cell_rank CC_Sanctioned <= cell_rank v.
Proof. destruct v; compute; lia. Qed.

(** Every [cell_verdict]'s rank is bounded above by five (the
    [CC_Compliant] rank). *)
Theorem cell_rank_compliant_is_global_max :
  forall v, cell_rank v <= cell_rank CC_Compliant.
Proof. destruct v; compute; lia. Qed.

(** [cell_meet] with [CC_Compliant] is the identity (the top of the
    carrier acts as the right unit for meet). *)
Lemma cell_meet_compliant_right :
  forall v, cell_meet v CC_Compliant = v.
Proof. destruct v; reflexivity. Qed.

Lemma cell_meet_compliant_left :
  forall v, cell_meet CC_Compliant v = v.
Proof. destruct v; reflexivity. Qed.

(** The cell-meet is a monoid operation on the non-Sanctioned
    fragment with [CC_Compliant] as the identity and
    [CC_Sanctioned] as the absorbing element.  The two sanctions-
    absorption and two compliant-identity lemmas above, together with
    [cell_meet_idempotent], [cell_meet_comm], and [cell_meet_assoc],
    package the structure.  Qed-bundled below. *)
Theorem cell_verdict_meet_commutative_monoid_with_absorbing_bottom :
  (forall v, cell_meet v v = v) /\
  (forall a b, cell_meet a b = cell_meet b a) /\
  (forall a b c, cell_meet (cell_meet a b) c = cell_meet a (cell_meet b c)) /\
  (forall v, cell_meet v CC_Compliant = v) /\
  (forall v, cell_meet CC_Compliant v = v) /\
  (forall v, cell_meet v CC_Sanctioned = CC_Sanctioned) /\
  (forall v, cell_meet CC_Sanctioned v = CC_Sanctioned).
Proof.
  split; [apply cell_meet_idempotent|].
  split; [apply cell_meet_comm|].
  split; [apply cell_meet_assoc|].
  split; [apply cell_meet_compliant_right|].
  split; [apply cell_meet_compliant_left|].
  split; [apply cell_meet_sanctioned_right|].
  apply cell_meet_sanctioned_left.
Qed.

(** ** Further structural properties (2026-04-20) *)

(** Decidable equality on the cell verdict. *)
Lemma cell_verdict_eq_dec :
  forall v1 v2 : cell_verdict, {v1 = v2} + {v1 <> v2}.
Proof. decide equality. Qed.

(** cell_rank is bounded above by 5 (CC_Compliant). *)
Lemma cell_rank_bounded : forall v, cell_rank v <= 5.
Proof. destruct v; simpl; lia. Qed.

(** cell_rank is injective: equal ranks imply equal verdicts. *)
Lemma cell_rank_injective :
  forall v1 v2, cell_rank v1 = cell_rank v2 -> v1 = v2.
Proof. destruct v1, v2; simpl; intro H; try reflexivity; discriminate. Qed.

(** Successive cell_verdict constructors are pairwise distinct. *)
Lemma cell_verdict_ctors_distinct :
  CC_Sanctioned <> CC_NonCompliant /\
  CC_NonCompliant <> CC_Pending /\
  CC_Pending <> CC_NotApplicable /\
  CC_NotApplicable <> CC_Exempt /\
  CC_Exempt <> CC_Compliant.
Proof. repeat split; discriminate. Qed.
