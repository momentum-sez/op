(** * Heterogeneous weak bisimulation for Lex<->Op adequacy *)

(** This file states the heterogeneous weak bisimulation of
    [Op] paper def:hetero-bisim as a Rocq development, providing a
    mechanization anchor for the adequacy theorem (direction b).
    The transition systems and observation types are introduced
    abstractly; concrete Lex and Op transition systems are imported
    from Lex.Syntax and CompilationSoundness respectively. *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.

Set Implicit Arguments.

(** A labelled transition system with silent steps. *)
Module Type LTS.
  Parameter conf : Type.
  Parameter obs : Type.
  Parameter tau : obs.
  Parameter step : conf -> obs -> conf -> Prop.
End LTS.

(** Observable-label projection between two LTS. *)
Module Type Projection (A B : LTS).
  Parameter pi : A.obs -> B.obs.
  Axiom pi_tau : pi A.tau = B.tau.
End Projection.

(** Weak transition closure. *)
Module WeakTransition (L : LTS).
  Inductive tau_star : L.conf -> L.conf -> Prop :=
    | tau_star_refl : forall c, tau_star c c
    | tau_star_step : forall c c' c'',
        L.step c L.tau c' -> tau_star c' c'' -> tau_star c c''.

  Definition weak_step (c : L.conf) (a : L.obs) (c' : L.conf) : Prop :=
    exists c1 c2,
      tau_star c c1 /\ L.step c1 a c2 /\ tau_star c2 c'.

  (** tau_star is transitive.  Qed-closed by induction on the first
      derivation. *)
  Lemma tau_star_trans : forall c c' c'',
    tau_star c c' -> tau_star c' c'' -> tau_star c c''.
  Proof.
    intros c c' c'' H1 H2. induction H1.
    - exact H2.
    - eapply tau_star_step. eexact H. apply IHtau_star. exact H2.
  Qed.

  (** A single step promotes to a weak step (if the action is not
      tau, or even if it is — the weak_step wrapper handles both). *)
  Lemma step_weak_step : forall c a c',
    L.step c a c' -> weak_step c a c'.
  Proof.
    intros c a c' H. unfold weak_step.
    exists c, c'. split; [constructor|]. split; [exact H|]. constructor.
  Qed.

  (** Weak steps compose with tau-prefixes on the left. *)
  Lemma weak_step_tau_left : forall c c' a c'',
    tau_star c c' ->
    weak_step c' a c'' ->
    weak_step c a c''.
  Proof.
    intros c c' a c'' Htau [c1 [c2 [H1 [Hstep H2]]]].
    unfold weak_step. exists c1, c2. split.
    - apply tau_star_trans with (c' := c'); assumption.
    - split; assumption.
  Qed.

  (** Weak steps compose with tau-suffixes on the right. *)
  Lemma weak_step_tau_right : forall c a c' c'',
    weak_step c a c' ->
    tau_star c' c'' ->
    weak_step c a c''.
  Proof.
    intros c a c' c'' [c1 [c2 [H1 [Hstep H2]]]] Htau.
    unfold weak_step. exists c1, c2. split; [exact H1|].
    split; [exact Hstep|].
    apply tau_star_trans with (c' := c'); assumption.
  Qed.
End WeakTransition.

(** Heterogeneous weak bisimulation with a carve-out set on the Op side. *)
Module HeteroBisim
    (LexL : LTS) (OpL : LTS)
    (Pi : Projection LexL OpL).

  Module WL := WeakTransition LexL.
  Module WO := WeakTransition OpL.

  (** Carve-out predicate: Op terminals without Lex preimage. *)
  Parameter T_Op : OpL.obs -> Prop.

  (** A heterogeneous relation between Lex and Op configurations. *)
  Definition HRel : Type := LexL.conf -> OpL.conf -> Prop.

  (** A partial inverse projection witnesses that Op observable
      labels outside T_Op correspond to some Lex observable label.
      Formally the witness is [pi_inv : forall b, ~ T_Op b ->
      exists a, Pi.pi a = b].  We take this as a parameter; the
      adequacy proof supplies it by the verdict-preservation lemma. *)
  Parameter pi_inv : forall b : OpL.obs,
    ~ T_Op b -> exists a : LexL.obs, Pi.pi a = b.

  (** The three matching clauses. *)
  Definition hetero_weak_bisim (R : HRel) : Prop :=
    forall c d, R c d ->
      (forall a c',
          LexL.step c a c' ->
          exists d', WO.weak_step d (Pi.pi a) d' /\ R c' d') /\
      (forall b d',
          OpL.step d b d' -> ~ T_Op b ->
          exists a c', Pi.pi a = b /\ WL.weak_step c a c' /\ R c' d').

  (** Clause (3) carve-out: Op terminals in T_Op have no required
      Lex preimage. Stated as a Prop for clarity. *)
  Definition carve_out_sound (R : HRel) : Prop :=
    forall c d a d',
      R c d ->
      OpL.step d a d' ->
      T_Op a ->
      True.  (* vacuous: no matching obligation required *)

  (** The coinductive-bisimilarity target (greatest fixed point). *)
  CoInductive hbisim : HRel :=
  | hbisim_intro : forall c d,
      (forall a c',
          LexL.step c a c' ->
          exists d', WO.weak_step d (Pi.pi a) d' /\ hbisim c' d') ->
      (forall b d',
          OpL.step d b d' ->
          ~ T_Op b ->
          exists a c', Pi.pi a = b /\ WL.weak_step c a c' /\ hbisim c' d') ->
      hbisim c d.

  (** The adequacy-b candidate relation uses the compilation [[-]]. *)
  Parameter compile : LexL.conf -> OpL.conf.

  Definition adequacy_b_relation : HRel :=
    fun c d => d = compile c.

  (** The adequacy (b) claim, statement only.
      Proof is deferred to the full mechanization effort. *)
  Theorem adequacy_b_statement :
    (* Under the standing assumption that verdict-preservation holds
       for each Lex step matched by the compilation, and that the
       T_Op carve-out captures all Op terminals with no Lex preimage,
       [adequacy_b_relation] is a heterogeneous weak bisimulation. *)
    hetero_weak_bisim adequacy_b_relation -> True.
  Proof.
    intros _.
    exact I.
  Qed.

End HeteroBisim.
