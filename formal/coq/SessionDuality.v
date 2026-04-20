(** * Binary session-type duality involution (Qed-closed) *)

(** Mechanizes the binary-session duality of op.tex §4.5
    (cross-zone commit as a binary session).  Local types form
    the Honda-Vasconcelos-Kubo discipline with send, receive,
    internal choice, external choice, recursion, variable, and
    end.  Duality is an involution: dual(dual(L)) = L.  All
    theorems Qed-closed by structural induction on local types. *)

Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.

(** Payload types are abstract (parameter). *)
Parameter payload : Type.

(** Labels for internal/external choice. *)
Definition label : Type := nat.

(** Recursion variable names. *)
Definition rvar : Type := nat.

(** Binary-session local types.  We model the bilateral form
    used in the corridor protocol: send/receive are single-label,
    and internal/external choice carry label-indexed continuations. *)
Inductive ltype : Type :=
  | L_Send : label -> payload -> ltype -> ltype
  | L_Recv : label -> payload -> ltype -> ltype
  | L_Select : list (label * payload * ltype) -> ltype
  | L_Branch : list (label * payload * ltype) -> ltype
  | L_Mu : rvar -> ltype -> ltype
  | L_Var : rvar -> ltype
  | L_End : ltype.

(** Dual of a local type: swap send/receive, swap select/branch.
    Recursion and end pass through unchanged. *)
Fixpoint dual (L : ltype) : ltype :=
  match L with
  | L_Send l t K => L_Recv l t (dual K)
  | L_Recv l t K => L_Send l t (dual K)
  | L_Select brs => L_Branch (map (fun b : label * payload * ltype =>
       let '(l, t, K) := b in (l, t, dual K)) brs)
  | L_Branch brs => L_Select (map (fun b : label * payload * ltype =>
       let '(l, t, K) := b in (l, t, dual K)) brs)
  | L_Mu x K => L_Mu x (dual K)
  | L_Var x => L_Var x
  | L_End => L_End
  end.

(** Helper: dual-map on branches is an involution. *)
Lemma dual_branch_map_involution :
  forall brs,
    (forall b, In b brs -> dual (dual (snd b)) = snd b) ->
    map (fun b : label * payload * ltype =>
       let '(l, t, K) := b in (l, t, dual K))
        (map (fun b : label * payload * ltype =>
       let '(l, t, K) := b in (l, t, dual K)) brs)
    = brs.
Proof.
  induction brs as [|b brs IH]; intros H; simpl.
  - reflexivity.
  - destruct b as [[l t] K]. simpl.
    assert (Hk : dual (dual K) = K).
    { apply (H (l, t, K)). left. reflexivity. }
    rewrite Hk. rewrite IH. reflexivity.
    intros b Hin. apply H. right. exact Hin.
Qed.

(** Duality is an involution: dual (dual L) = L.  Proved by a
    directly-written fixpoint that recurses on L and, at the branch
    constructors, walks the branch list inline.  The guard checker
    accepts [snd b] as a structural subterm of [L_Select brs] /
    [L_Branch brs]. *)
Fixpoint dual_involution (L : ltype) : dual (dual L) = L.
Proof.
  destruct L as [l t K | l t K | brs | brs | x K | x | ]; simpl.
  - rewrite (dual_involution K). reflexivity.
  - rewrite (dual_involution K). reflexivity.
  - f_equal. induction brs as [|b brs' IH]; simpl; [reflexivity|].
    destruct b as [[lb tb] Kb]. simpl. rewrite (dual_involution Kb).
    rewrite IH. reflexivity.
  - f_equal. induction brs as [|b brs' IH]; simpl; [reflexivity|].
    destruct b as [[lb tb] Kb]. simpl. rewrite (dual_involution Kb).
    rewrite IH. reflexivity.
  - rewrite (dual_involution K). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** End is self-dual. *)
Lemma dual_end : dual L_End = L_End.
Proof. reflexivity. Qed.

(** Variables are self-dual. *)
Lemma dual_var : forall x, dual (L_Var x) = L_Var x.
Proof. reflexivity. Qed.

(** Send and receive are dual to each other. *)
Lemma dual_send_recv : forall l t K,
  dual (L_Send l t K) = L_Recv l t (dual K).
Proof. reflexivity. Qed.

Lemma dual_recv_send : forall l t K,
  dual (L_Recv l t K) = L_Send l t (dual K).
Proof. reflexivity. Qed.

(** Select and branch are dual to each other. *)
Lemma dual_select : forall brs,
  dual (L_Select brs) = L_Branch (map (fun b : label * payload * ltype =>
       let '(l, t, K) := b in (l, t, dual K)) brs).
Proof. reflexivity. Qed.

Lemma dual_branch : forall brs,
  dual (L_Branch brs) = L_Select (map (fun b : label * payload * ltype =>
       let '(l, t, K) := b in (l, t, dual K)) brs).
Proof. reflexivity. Qed.

(** Recursion passes through duality unchanged on the binder. *)
Lemma dual_mu : forall x K, dual (L_Mu x K) = L_Mu x (dual K).
Proof. reflexivity. Qed.

(** Duality is injective: [dual L = dual M] implies [L = M].
    Follows from the involution: if [dual L = dual M], then
    [L = dual (dual L) = dual (dual M) = M]. *)
Theorem dual_injective : forall L M,
  dual L = dual M -> L = M.
Proof.
  intros L M H.
  rewrite <- (dual_involution L), <- (dual_involution M).
  f_equal. exact H.
Qed.

(** Duality is a bijection on [ltype].  Paired with
    [dual_involution] and [dual_injective], this is the surjective
    companion: every [ltype] has a dual pre-image (itself, via
    another application of dual). *)
Theorem dual_surjective : forall L,
  exists M, dual M = L.
Proof.
  intro L. exists (dual L). apply dual_involution.
Qed.

(** End and [L_Var] are the only [ltype] shapes self-dual under
    the syntactic duality operator. *)
Lemma end_self_dual : dual L_End = L_End.
Proof. reflexivity. Qed.

Lemma var_self_dual : forall x, dual (L_Var x) = L_Var x.
Proof. reflexivity. Qed.

(** Any fixed point of [dual] must be either [L_End] or [L_Var x].
    This is the syntactic characterisation of self-duality.
    [L_Mu] is NOT self-dual under this operator because [dual]
    descends into the body; a recursion [mu x. Send l t x] is NOT
    equal to its dual [mu x. Recv l t x].

    We don't prove the full "only if" direction here (it would
    require reasoning about [dual]'s non-self-inverse action on
    Send/Recv, Select/Branch, and under Mu); instead we surface
    the direct observation that end and bare var are self-dual
    as named lemmas above. *)

(** ** Concrete non-self-dual witnesses (2026-04-20) *)

(** L_Send with a continuation that duals is NOT self-dual.  Concrete
    witness that duality is a non-trivial operation on most [ltype]s. *)
Theorem send_not_self_dual :
  forall l t, dual (L_Send l t L_End) <> L_Send l t L_End.
Proof. intros l t. simpl. discriminate. Qed.

(** L_Recv is never self-dual for the same reason. *)
Theorem recv_not_self_dual :
  forall l t, dual (L_Recv l t L_End) <> L_Recv l t L_End.
Proof. intros l t. simpl. discriminate. Qed.

(** L_Mu is not self-dual in general: body flips send/recv. *)
Theorem mu_send_not_self_dual :
  forall x l t, dual (L_Mu x (L_Send l t (L_Var x)))
             <> L_Mu x (L_Send l t (L_Var x)).
Proof. intros x l t. simpl. discriminate. Qed.

(** [dual] on L_Send l t K produces L_Recv l t (dual K). *)
Theorem dual_send_structure :
  forall l t K, exists K', dual (L_Send l t K) = L_Recv l t K'.
Proof.
  intros l t K. exists (dual K). reflexivity.
Qed.

(** [dual] on L_Recv l t K produces L_Send l t (dual K). *)
Theorem dual_recv_structure :
  forall l t K, exists K', dual (L_Recv l t K) = L_Send l t K'.
Proof.
  intros l t K. exists (dual K). reflexivity.
Qed.

