(** * Bilateral MPST projection and duality (Qed-closed) *)

(** Mechanizes the bilateral MPST projection of op.tex §4.5
    (corridor global type with two roles) and closes the
    fundamental duality lemma: in a bilateral-only protocol,
    projection onto the initiator is dual to projection onto the
    responder.

    We restrict to a bilateral global type where every
    transmission is either I->R or R->I, so the uninvolved case
    never fires.  All theorems Qed-closed. *)

Require Import Coq.Lists.List.
Import ListNotations.

(** Not using Set Implicit Arguments here: the branch-map helpers
    quantify over [lb, tb, Gb] explicitly, and implicit-argument
    inference has trouble under the joint-induction rewrite. *)

(** Two roles for the bilateral corridor: Initiator and Responder. *)
Inductive role : Type := Initiator | Responder.

Definition role_eq_dec : forall r1 r2 : role, {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.

(** The "other role" function. *)
Definition other (r : role) : role :=
  match r with
  | Initiator => Responder
  | Responder => Initiator
  end.

Lemma other_involution : forall r, other (other r) = r.
Proof. destruct r; reflexivity. Qed.

Lemma other_neq : forall r, other r <> r.
Proof. destruct r; discriminate. Qed.

(** Payload type (abstract). *)
Parameter payload : Type.

(** Label type. *)
Definition label : Type := nat.

(** Bilateral global types: transmission between the two roles
    encoded as a direction tag, so there is no third-role case. *)
Inductive direction : Type := I2R | R2I.

Definition sender (d : direction) : role :=
  match d with I2R => Initiator | R2I => Responder end.

Definition receiver (d : direction) : role :=
  match d with I2R => Responder | R2I => Initiator end.

Lemma sender_receiver_other : forall d,
  receiver d = other (sender d).
Proof. destruct d; reflexivity. Qed.

Lemma sender_other_receiver : forall d,
  sender d = other (receiver d).
Proof. destruct d; reflexivity. Qed.

(** Bilateral global type: every transmission has a direction
    rather than two arbitrary roles, enforcing the bilateral
    structure syntactically. *)
Inductive bgtype : Type :=
  | BG_Send : direction -> label -> payload -> bgtype -> bgtype
  | BG_Branch : direction -> list (label * payload * bgtype) -> bgtype
  | BG_End : bgtype.

(** Local types. *)
Inductive ltype : Type :=
  | L_Send : label -> payload -> ltype -> ltype
  | L_Recv : label -> payload -> ltype -> ltype
  | L_Select : list (label * payload * ltype) -> ltype
  | L_Branch : list (label * payload * ltype) -> ltype
  | L_End : ltype.

(** Duality. *)
Fixpoint dual (L : ltype) : ltype :=
  match L with
  | L_Send l t K => L_Recv l t (dual K)
  | L_Recv l t K => L_Send l t (dual K)
  | L_Select brs => L_Branch (map (fun b : label * payload * ltype =>
                                     let '(l, t, K) := b in (l, t, dual K)) brs)
  | L_Branch brs => L_Select (map (fun b : label * payload * ltype =>
                                     let '(l, t, K) := b in (l, t, dual K)) brs)
  | L_End => L_End
  end.

(** Projection of a bilateral global type onto a role. *)
Fixpoint bproject (G : bgtype) (r : role) : ltype :=
  match G with
  | BG_Send d l t G' =>
      if role_eq_dec r (sender d) then L_Send l t (bproject G' r)
      else L_Recv l t (bproject G' r)
  | BG_Branch d brs =>
      if role_eq_dec r (sender d) then
        L_Select (map (fun b : label * payload * bgtype =>
                         let '(l, t, G') := b in (l, t, bproject G' r)) brs)
      else
        L_Branch (map (fun b : label * payload * bgtype =>
                         let '(l, t, G') := b in (l, t, bproject G' r)) brs)
  | BG_End => L_End
  end.

(** Duality is an involution. *)
Fixpoint dual_involution (L : ltype) : dual (dual L) = L.
Proof.
  destruct L as [l t K | l t K | brs | brs | ]; simpl.
  - rewrite (dual_involution K). reflexivity.
  - rewrite (dual_involution K). reflexivity.
  - f_equal. induction brs as [|b brs' IH]; simpl; [reflexivity|].
    destruct b as [[lb tb] Kb]. simpl. rewrite (dual_involution Kb).
    rewrite IH. reflexivity.
  - f_equal. induction brs as [|b brs' IH]; simpl; [reflexivity|].
    destruct b as [[lb tb] Kb]. simpl. rewrite (dual_involution Kb).
    rewrite IH. reflexivity.
  - reflexivity.
Qed.

(** Main theorem: bilateral projection commutes with duality.

    Both directions of the bilateral-duality statement proved
    jointly by recursion on G.  This is the bilateral-case MPST
    coherence theorem (Honda, Yoshida, Carbone POPL 2008
    specialized to N=2). *)
(** Main theorem: bilateral projection commutes with duality.
    Proved by Fixpoint on G, with the branch list walked inline
    so the guard checker recognizes each [Gb] as a structural
    subterm of [BG_Branch d brs].  In each branch rewrite exactly
    one hypothesis at a time to avoid loops. *)
Fixpoint bilateral_duality_joint (G : bgtype) {struct G}
  : bproject G Initiator = dual (bproject G Responder) /\
    bproject G Responder = dual (bproject G Initiator).
Proof.
  destruct G as [d l t G' | d brs | ].
  - (** BG_Send case. *)
    pose proof (bilateral_duality_joint G') as [HI HR].
    destruct d; simpl; split; f_equal; congruence.
  - (** BG_Branch case.  Inline branch-list recursion. *)
    split.
    + (** Initiator projection = dual (Responder projection). *)
      destruct d; simpl; f_equal;
      (induction brs as [|b brs' IH]; simpl; [reflexivity|];
       destruct b as [[lb tb] Gb]; simpl;
       destruct (bilateral_duality_joint Gb) as [HIb _];
       rewrite HIb; f_equal; exact IH).
    + (** Responder projection = dual (Initiator projection). *)
      destruct d; simpl; f_equal;
      (induction brs as [|b brs' IH]; simpl; [reflexivity|];
       destruct b as [[lb tb] Gb]; simpl;
       destruct (bilateral_duality_joint Gb) as [_ HRb];
       rewrite HRb; f_equal; exact IH).
  - (** BG_End case. *)
    split; reflexivity.
Qed.

Theorem bilateral_duality :
  forall G, bproject G Initiator = dual (bproject G Responder).
Proof.
  intro G. destruct (bilateral_duality_joint G) as [H _]. exact H.
Qed.

Theorem bilateral_duality_sym :
  forall G, bproject G Responder = dual (bproject G Initiator).
Proof.
  intro G. destruct (bilateral_duality_joint G) as [_ H]. exact H.
Qed.

Theorem bilateral_mpst_coherence :
  forall G,
    dual (bproject G Initiator) = bproject G Responder /\
    dual (bproject G Responder) = bproject G Initiator.
Proof.
  intro G. destruct (bilateral_duality_joint G) as [HI HR].
  rewrite HI. rewrite HR. split.
  - rewrite dual_involution. reflexivity.
  - rewrite dual_involution. reflexivity.
Qed.

(** Projection commutes with duality at the role level:
    bproject G (other r) = dual (bproject G r). *)
Theorem bprojection_dual :
  forall G r, bproject G (other r) = dual (bproject G r).
Proof.
  intros G r. destruct r.
  - simpl. apply bilateral_duality_sym.
  - simpl. apply bilateral_duality.
Qed.
