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
