(** * LexVerdictEmbedding.v — Embedding of the Lex per-coordinate
    five-element verdict chain into the Op compliance-context six-valued
    cell_verdict.

    This file closes the E1 alignment obligation identified by the
    2026-04-20 platonic-ideal kickstart: the Lex paper and
    [~/kernel/formal/coq/Lex/VerdictHeyting.v] mechanise a five-element
    chain {NonCompliant < Pending < NotApplicable < Exempt < Compliant}
    as the per-(entity, jurisdiction, domain) verdict.  The Op operational
    layer in [ComplianceContext.v] adds a sixth absorbing-bottom
    [CC_Sanctioned] to represent sanctions-blocked execution paths,
    producing the six-valued [cell_verdict].

    Because the op/formal/coq build does not import ~/kernel/formal/coq/Lex
    load paths, we duplicate the Lex verdict carrier locally as
    [lex_verdict] with identical constructors and ordering.  The
    embedding [lex_to_op] maps the five Lex values to the five non-
    Sanctioned values of [cell_verdict] in rank-ascending order, shifted
    up by one position to accommodate the absorbing Sanctioned bottom.

    Three facts are proved, all Qed-closed by exhaustive case analysis:

    - [lex_to_op_never_sanctioned] : the embedding never produces
      [CC_Sanctioned].  The Sanctioned value is out of scope for any
      verdict originating in Lex; it is introduced only by the Op layer's
      sanctions hard-block, which does not pass through Lex evaluation.

    - [lex_to_op_preserves_meet] : the embedding commutes with meet on
      the non-Sanctioned fragment.  Specifically,
      [lex_to_op (verdict_meet v1 v2) = cell_meet (lex_to_op v1) (lex_to_op v2)],
      so the five-chain Heyting meet and the six-valued operational
      meet agree modulo the embedding.

    - [lex_to_op_rank_monotone] : the embedding is strictly rank-monotone
      with a uniform shift: for every Lex verdict [v],
      [cell_rank (lex_to_op v) = S (lex_rank v)].  This witnesses that
      the Lex five-chain is isomorphic to the top five elements of the
      Op six-chain, with Sanctioned occupying the distinguished absorbing
      bottom.

    Together these establish that the Op six-valued operational verdict
    is a faithful extension of the Lex five-chain, adding one absorbing
    value for sanctions-blocked paths, not a reinterpretation of the Lex
    carrier.  The two Coq mechanisations are therefore compatible, and
    the Op paper's semantics is a proper operational refinement of the
    Lex verdict lattice. *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import ComplianceContext.

(** ** Local redefinition of the Lex five-element verdict *)

(** Identical to the [verdict] inductive in
    [~/kernel/formal/coq/Lex/VerdictHeyting.v].  The embedding below
    is purely structural, so duplicating the carrier here incurs no
    semantic cost. *)
Inductive lex_verdict : Type :=
  | LV_NonCompliant
  | LV_Pending
  | LV_NotApplicable
  | LV_Exempt
  | LV_Compliant.

Definition lex_rank (v : lex_verdict) : nat :=
  match v with
  | LV_NonCompliant  => 0
  | LV_Pending       => 1
  | LV_NotApplicable => 2
  | LV_Exempt        => 3
  | LV_Compliant     => 4
  end.

Definition lex_unrank (n : nat) : lex_verdict :=
  match n with
  | 0 => LV_NonCompliant
  | 1 => LV_Pending
  | 2 => LV_NotApplicable
  | 3 => LV_Exempt
  | _ => LV_Compliant
  end.

Definition verdict_meet (v1 v2 : lex_verdict) : lex_verdict :=
  lex_unrank (Nat.min (lex_rank v1) (lex_rank v2)).

(** ** Embedding from Lex five-chain to Op six-valued cell_verdict *)

(** Each Lex verdict maps to the corresponding [CC_*] constructor.
    The embedding is injective and skips [CC_Sanctioned] by
    construction. *)
Definition lex_to_op (v : lex_verdict) : cell_verdict :=
  match v with
  | LV_NonCompliant  => CC_NonCompliant
  | LV_Pending       => CC_Pending
  | LV_NotApplicable => CC_NotApplicable
  | LV_Exempt        => CC_Exempt
  | LV_Compliant     => CC_Compliant
  end.

(** ** The embedding never produces the absorbing Sanctioned bottom *)

Theorem lex_to_op_never_sanctioned :
  forall v, lex_to_op v <> CC_Sanctioned.
Proof. destruct v; discriminate. Qed.

(** ** The embedding is injective *)

Theorem lex_to_op_injective :
  forall v1 v2, lex_to_op v1 = lex_to_op v2 -> v1 = v2.
Proof. destruct v1, v2; simpl; intro H; inversion H; reflexivity. Qed.

(** ** Uniform rank shift *)

(** The Lex five-chain embeds into the top five positions of the Op
    six-chain; ranks shift up by one to accommodate
    [CC_Sanctioned = 0]. *)
Theorem lex_to_op_rank_monotone :
  forall v, cell_rank (lex_to_op v) = S (lex_rank v).
Proof. destruct v; reflexivity. Qed.

(** ** Meet preservation on the non-Sanctioned fragment *)

(** On the five Lex verdicts (never producing Sanctioned under the
    embedding), the five-chain Heyting meet and the six-valued
    operational meet agree up to the embedding.  Qed by case analysis
    over the twenty-five ordered pairs. *)
Theorem lex_to_op_preserves_meet :
  forall v1 v2,
    lex_to_op (verdict_meet v1 v2) =
    cell_meet (lex_to_op v1) (lex_to_op v2).
Proof.
  destruct v1, v2; compute; reflexivity.
Qed.

(** ** Bounds preservation *)

(** The Lex chain's top (LV_Compliant) maps to the Op chain's top
    (CC_Compliant) under the embedding.  This is the maximal value in
    both the Lex five-chain and the Op six-valued carrier when
    restricted to the non-Sanctioned fragment. *)
Theorem lex_to_op_preserves_top :
  lex_to_op LV_Compliant = CC_Compliant.
Proof. reflexivity. Qed.

(** The Lex chain's bottom (LV_NonCompliant) maps to the second-
    from-bottom of Op's carrier, NOT to CC_Sanctioned (which is Op's
    absorbing bottom but lies strictly below the image of
    [lex_to_op]).  This is the statement that the Lex five-chain
    embeds into the top-five positions of the Op six-valued carrier,
    with [CC_Sanctioned] reserved for sanctions-blocked paths that
    do not originate in Lex evaluation. *)
Theorem lex_to_op_bottom_above_sanctioned :
  cell_rank CC_Sanctioned < cell_rank (lex_to_op LV_NonCompliant).
Proof. compute. lia. Qed.

(** [lex_to_op] is rank-preserving up to the uniform shift, so every
    Lex chain element's image has strictly greater rank than
    [CC_Sanctioned]. *)
Theorem lex_to_op_image_above_sanctioned :
  forall v, cell_rank CC_Sanctioned < cell_rank (lex_to_op v).
Proof. destruct v; compute; lia. Qed.

(** Meet with [CC_Sanctioned] absorbs the embedded image to
    [CC_Sanctioned] itself, which is OUTSIDE the image of
    [lex_to_op].  This is the operational statement that sanctions-
    blocking leaves the Lex sub-lattice entirely. *)
Theorem lex_image_absorbed_by_sanctioned :
  forall v,
    cell_meet (lex_to_op v) CC_Sanctioned = CC_Sanctioned.
Proof. intro v. apply cell_meet_sanctioned_right. Qed.

Theorem sanctioned_absorbs_lex_image :
  forall v,
    cell_meet CC_Sanctioned (lex_to_op v) = CC_Sanctioned.
Proof. intro v. apply cell_meet_sanctioned_left. Qed.

(** ** Structural bijection on the non-Sanctioned fragment *)

(** Every non-Sanctioned [cell_verdict] has a unique preimage under
    [lex_to_op].  The reverse projection is a Qed-closed partial
    inverse that completes the bijection story. *)
Definition op_to_lex (c : cell_verdict) : option lex_verdict :=
  match c with
  | CC_NonCompliant  => Some LV_NonCompliant
  | CC_Pending       => Some LV_Pending
  | CC_NotApplicable => Some LV_NotApplicable
  | CC_Exempt        => Some LV_Exempt
  | CC_Compliant     => Some LV_Compliant
  | CC_Sanctioned    => None
  end.

(** [op_to_lex] is the left inverse of [lex_to_op]. *)
Theorem op_to_lex_left_inverse :
  forall v, op_to_lex (lex_to_op v) = Some v.
Proof. destruct v; reflexivity. Qed.

(** [op_to_lex] is the right inverse of [lex_to_op] on the
    non-Sanctioned fragment. *)
Theorem op_to_lex_right_inverse :
  forall c v,
    op_to_lex c = Some v ->
    lex_to_op v = c.
Proof. destruct c; simpl; intros v H; inversion H; reflexivity. Qed.

(** Sanctioned has no preimage — the reverse projection explicitly
    signals this with [None]. *)
Theorem op_to_lex_sanctioned_is_none :
  op_to_lex CC_Sanctioned = None.
Proof. reflexivity. Qed.

(** Surjectivity on the non-Sanctioned fragment: every non-Sanctioned
    [cell_verdict] is in the image of [lex_to_op]. *)
Theorem lex_to_op_surjective_on_non_sanctioned :
  forall c,
    c <> CC_Sanctioned ->
    exists v, lex_to_op v = c.
Proof.
  intros c Hne.
  destruct c; try congruence.
  - exists LV_Compliant. reflexivity.
  - exists LV_Exempt. reflexivity.
  - exists LV_NotApplicable. reflexivity.
  - exists LV_Pending. reflexivity.
  - exists LV_NonCompliant. reflexivity.
Qed.

(** ** Further properties of lex_rank and verdict_meet (2026-04-20) *)

(** lex_rank is bounded above by 4 (the rank of LV_Compliant). *)
Theorem lex_rank_bounded : forall v, lex_rank v <= 4.
Proof. destruct v; simpl; lia. Qed.

(** lex_rank is injective. *)
Theorem lex_rank_injective : forall v1 v2,
  lex_rank v1 = lex_rank v2 -> v1 = v2.
Proof. destruct v1, v2; simpl; intro H; try reflexivity; discriminate. Qed.

(** verdict_meet is idempotent. *)
Theorem verdict_meet_idempotent : forall v,
  verdict_meet v v = v.
Proof. destruct v; reflexivity. Qed.

(** verdict_meet is commutative. *)
Theorem verdict_meet_comm : forall v1 v2,
  verdict_meet v1 v2 = verdict_meet v2 v1.
Proof. destruct v1, v2; reflexivity. Qed.

(** lex_unrank is the left inverse of lex_rank. *)
Theorem lex_unrank_rank : forall v, lex_unrank (lex_rank v) = v.
Proof. destruct v; reflexivity. Qed.

(** lex_to_op preserves strict-less-than: if [lex_rank v1 < lex_rank v2]
    then the image ranks are also in strict order. *)
Theorem lex_to_op_preserves_strict_order :
  forall v1 v2,
    lex_rank v1 < lex_rank v2 ->
    cell_rank (lex_to_op v1) < cell_rank (lex_to_op v2).
Proof.
  intros v1 v2 H.
  rewrite (lex_to_op_rank_monotone v1), (lex_to_op_rank_monotone v2).
  lia.
Qed.

(** The embedding–reverse pair witnesses a structural bijection
    between the Lex five-chain and the non-Sanctioned fragment of the
    Op six-valued operational carrier.  Together with
    [lex_to_op_preserves_meet] and [lex_to_op_rank_monotone], this
    establishes that the two per-coordinate verdict algebras coincide
    on their shared domain; the Op algebra extends the Lex algebra by
    exactly one absorbing value, and the extension is a conservative
    addition with no reinterpretation of the embedded structure. *)

(** ** Summary

    [lex_to_op] is an injective, rank-shift-preserving, meet-preserving
    embedding from Lex's five-chain verdict into the non-Sanctioned
    fragment of Op's six-valued [cell_verdict].  The Op layer's
    [CC_Sanctioned] is genuinely new: an absorbing bottom introduced by
    sanctions hard-block paths that do not originate in Lex evaluation.
    The five-chain Heyting algebra of the Lex paper is preserved on the
    embedded fragment, and the six-valued operational lattice is a
    conservative extension adding exactly one absorbing value.

    This file, combined with
    [~/kernel/formal/coq/Lex/TensorAlignment.v] (which mechanises the
    relationship between the Lex five-chain and the SJN tensor-factor
    algebra with orthogonal applicability), completes the Coq witness
    that the three verdict mechanisations — Lex per-coordinate five-chain
    (VerdictHeyting.v), Op operational six-valued (ComplianceContext.v),
    SJN tensor-factor (TensorAlignment.v) — are mutually compatible
    views at distinct compositional levels, related by Qed-closed
    projections on their shared sub-structures and separated by F144
    outside the Applicable fragment. *)

(** ** Further embedding properties (2026-04-20) *)

(** Decidable equality on lex_verdict. *)
Lemma lex_verdict_eq_dec :
  forall v1 v2 : lex_verdict, {v1 = v2} + {v1 <> v2}.
Proof. decide equality. Qed.

(** The five lex_verdict constructors are pairwise distinct. *)
Lemma lex_verdict_ctors_distinct :
  LV_NonCompliant <> LV_Pending /\
  LV_Pending <> LV_NotApplicable /\
  LV_NotApplicable <> LV_Exempt /\
  LV_Exempt <> LV_Compliant.
Proof. repeat split; discriminate. Qed.

(** lex_to_op is a function (i.e., it's total). *)
Lemma lex_to_op_total :
  forall v, exists c, lex_to_op v = c.
Proof. intros v. exists (lex_to_op v). reflexivity. Qed.

(** Every Lex verdict has a concrete Op image (not CC_Sanctioned). *)
Theorem lex_verdict_image_non_sanctioned :
  forall v, lex_to_op v <> CC_Sanctioned.
Proof. exact lex_to_op_never_sanctioned. Qed.

(** op_to_lex composed with lex_to_op is the identity (left inverse
    alias surfaced for citation). *)
Theorem embedding_left_inverse :
  forall v, op_to_lex (lex_to_op v) = Some v.
Proof. exact op_to_lex_left_inverse. Qed.
