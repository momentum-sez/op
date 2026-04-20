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
