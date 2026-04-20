(** * Canonical encoding uniqueness (Qed-closed) *)

(** Mechanizes the content-addressability claim of op.tex §6
    (``Receipt CBOR wire format''): well-formed receipts encode
    to canonical byte strings, and distinct receipts have
    distinct encodings.  This is the invariant that makes
    hash-based content-addressing sound: a hash collision on
    encoded receipts requires a collision on the hash function,
    not a canonicalization ambiguity.

    We mechanize a scale-model of the CBOR receipt format: a
    three-field record (entity, operation, verdict) encoded as
    a canonical list of naturals with fixed field order.  All
    theorems Qed-closed. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Set Implicit Arguments.

(** A minimal verdict type (smaller than the full 6-element
    compliance one for clarity of the encoding proof). *)
Inductive verdict : Type :=
  | V_Compliant
  | V_NonCompliant
  | V_Sanctioned.

Definition verdict_eq_dec : forall v1 v2 : verdict, {v1 = v2} + {v1 <> v2}.
Proof. decide equality. Defined.

Definition verdict_encode (v : verdict) : nat :=
  match v with
  | V_Compliant => 0
  | V_NonCompliant => 1
  | V_Sanctioned => 2
  end.

Definition verdict_decode (n : nat) : option verdict :=
  match n with
  | 0 => Some V_Compliant
  | 1 => Some V_NonCompliant
  | 2 => Some V_Sanctioned
  | _ => None
  end.

Lemma verdict_roundtrip : forall v,
  verdict_decode (verdict_encode v) = Some v.
Proof. destruct v; reflexivity. Qed.

Lemma verdict_encode_injective : forall v1 v2,
  verdict_encode v1 = verdict_encode v2 -> v1 = v2.
Proof. destruct v1, v2; simpl; intro H; try reflexivity; discriminate. Qed.

(** A receipt: entity id + operation code + verdict.  All fields
    canonically ordered. *)
Record receipt : Type := mk_receipt {
  r_entity : nat;
  r_op : nat;
  r_verdict : verdict;
}.

(** Canonical encoding: a fixed-order list of naturals.  The
    ordering is part of the canonicalization contract: the same
    receipt always produces the same list. *)
Definition encode (r : receipt) : list nat :=
  [r_entity r; r_op r; verdict_encode (r_verdict r)].

(** Canonical decoding: parse the fixed-order list back.  Fails
    on malformed lists. *)
Definition decode (ns : list nat) : option receipt :=
  match ns with
  | [e; o; vn] =>
      match verdict_decode vn with
      | Some v => Some (mk_receipt e o v)
      | None => None
      end
  | _ => None
  end.

(** The fundamental roundtrip theorem. *)
Theorem encode_decode_roundtrip : forall r,
  decode (encode r) = Some r.
Proof.
  intros [e o v]. unfold encode, decode. simpl.
  rewrite verdict_roundtrip. reflexivity.
Qed.

(** Canonical encoding is injective: distinct receipts have
    distinct encodings.  This is the content-addressability
    claim: hash(encode r) uniquely identifies r. *)
Theorem encode_injective : forall r1 r2,
  encode r1 = encode r2 -> r1 = r2.
Proof.
  intros [e1 o1 v1] [e2 o2 v2] H.
  unfold encode in H. simpl in H.
  inversion H; subst.
  apply verdict_encode_injective in H3. subst.
  reflexivity.
Qed.

(** Corollary: the canonical-encoding map is a bijection onto
    its image. *)
Theorem encode_is_bijection : forall r1 r2,
  encode r1 = encode r2 <-> r1 = r2.
Proof.
  intros r1 r2. split.
  - apply encode_injective.
  - intro H. subst. reflexivity.
Qed.

(** Encode produces a fixed-length list (length 3). *)
Theorem encode_length : forall r, length (encode r) = 3.
Proof. intros [e o v]. reflexivity. Qed.

(** Decode is partial: non-length-3 lists fail. *)
Theorem decode_only_on_length_3 : forall ns r,
  decode ns = Some r -> length ns = 3.
Proof.
  intros ns r H. unfold decode in H.
  destruct ns as [|a [|b [|c [|d ?]]]];
    try discriminate.
  reflexivity.
Qed.

(** Decode-encode roundtrip on the canonical subset: if decode
    succeeds, encode of the result reproduces the input list. *)
Theorem decode_encode_roundtrip : forall ns r,
  decode ns = Some r -> encode r = ns.
Proof.
  intros ns r H. unfold decode in H.
  destruct ns as [|a [|b [|c [|d ?]]]];
    try discriminate.
  destruct (verdict_decode c) as [v|] eqn:Hv; try discriminate.
  inversion H; subst. clear H.
  unfold encode. simpl.
  f_equal. f_equal. f_equal.
  (** Prove verdict_encode v = c given verdict_decode c = Some v. *)
  destruct c as [|c1].
  - simpl in Hv. inversion Hv; subst. reflexivity.
  - destruct c1 as [|c2].
    + simpl in Hv. inversion Hv; subst. reflexivity.
    + destruct c2 as [|c3].
      * simpl in Hv. inversion Hv; subst. reflexivity.
      * simpl in Hv. discriminate.
Qed.

(** Content-addressability: two receipts with the same encoding
    are the same receipt; equivalently, a hash collision on
    encodings requires a collision on the abstract hash, not a
    canonicalization ambiguity. *)
Theorem content_addressable : forall r1 r2,
  encode r1 = encode r2 -> r1 = r2.
Proof. apply encode_injective. Qed.

(** * Further canonicity properties (2026-04-20)

    The following theorems sharpen content-addressability with
    pointwise-decode determinism, range-restriction on the verdict
    tag, and structural invariance of the canonical field order. *)

(** Verdict encoding is bounded: a valid verdict tag is at most 2. *)
Theorem verdict_encode_bounded :
  forall v, verdict_encode v <= 2.
Proof. destruct v; simpl; auto. Qed.

(** Verdict decode is partial outside the range [0,2]: any input
    [>= 3] decodes to [None]. *)
Theorem verdict_decode_out_of_range :
  forall n, n >= 3 -> verdict_decode n = None.
Proof.
  intros n Hge. destruct n as [|[|[|n']]]; try lia.
  reflexivity.
Qed.

(** Verdict decode is injective on the valid range. *)
Theorem verdict_decode_injective :
  forall n1 n2 v,
    verdict_decode n1 = Some v ->
    verdict_decode n2 = Some v ->
    n1 = n2.
Proof.
  intros n1 n2 v H1 H2.
  destruct n1 as [|[|[|n1']]]; try discriminate;
    destruct n2 as [|[|[|n2']]]; try discriminate;
    simpl in *; inversion H1; inversion H2; subst;
    try reflexivity; try discriminate.
Qed.

(** Decode is deterministic: a given list has at most one
    decoding.  Follows from the structural match. *)
Theorem decode_deterministic :
  forall ns r1 r2,
    decode ns = Some r1 ->
    decode ns = Some r2 ->
    r1 = r2.
Proof.
  intros ns r1 r2 H1 H2. rewrite H1 in H2. inversion H2. reflexivity.
Qed.

(** A valid encoding has its entity field at list position 0. *)
Theorem encode_entity_at_zero :
  forall r, nth_error (encode r) 0 = Some (r_entity r).
Proof. intros [e o v]. reflexivity. Qed.

(** A valid encoding has its operation field at list position 1. *)
Theorem encode_op_at_one :
  forall r, nth_error (encode r) 1 = Some (r_op r).
Proof. intros [e o v]. reflexivity. Qed.

(** A valid encoding has its verdict-tag at list position 2. *)
Theorem encode_verdict_at_two :
  forall r, nth_error (encode r) 2 = Some (verdict_encode (r_verdict r)).
Proof. intros [e o v]. reflexivity. Qed.

(** Two encodings agreeing at every position are the same encoding. *)
Theorem encode_pointwise_eq :
  forall r1 r2,
    nth_error (encode r1) 0 = nth_error (encode r2) 0 ->
    nth_error (encode r1) 1 = nth_error (encode r2) 1 ->
    nth_error (encode r1) 2 = nth_error (encode r2) 2 ->
    encode r1 = encode r2.
Proof.
  intros [e1 o1 v1] [e2 o2 v2] H0 H1 H2.
  simpl in *. inversion H0; inversion H1; inversion H2; subst.
  apply verdict_encode_injective in H5. subst. reflexivity.
Qed.

(** Encoding produces no zero-length list: every valid receipt
    has a non-empty encoding. *)
Theorem encode_nonempty :
  forall r, encode r <> [].
Proof. intros [e o v]. discriminate. Qed.
