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
