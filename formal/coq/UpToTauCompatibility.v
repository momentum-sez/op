(** * Up-to-tau compatibility for Op weak bisimulation *)

(** This file states the up-to-tau compatibility lemma of
    [Op] paper lem:up-to-tau-compatible as a Rocq development.
    The Pous-Sangiorgi compatibility criterion for an up-to function
    [f] on a functor [F] is [f \circ F \subseteq F \circ f]; for
    [tau(R) = =>_tau o R o =>_tau] the criterion is discharged by
    Op's determinism + finite-gas termination. *)

Require Import Coq.Relations.Relation_Definitions.

Set Implicit Arguments.

(** Abstract LTS with tau as in HeteroBisimulation.v. *)
Module Type LTS.
  Parameter conf : Type.
  Parameter obs : Type.
  Parameter tau : obs.
  Parameter step : conf -> obs -> conf -> Prop.

  (** Hypotheses required by up-to-tau compatibility. *)
  Axiom step_deterministic :
    forall c a c1 c2,
      step c a c1 -> step c a c2 -> c1 = c2.

  (** Tau-termination as an abstract well-founded order on
      configurations: there exists a measure mu : conf -> nat such
      that every tau-step strictly decreases the measure.  This is
      the abstract form of Op's finite-gas termination
      (thm:op-progress). *)
  Parameter tau_measure : conf -> nat.
  Axiom tau_decreases :
    forall c c', step c tau c' -> tau_measure c' < tau_measure c.
End LTS.

Module UpToTau (L : LTS).

  (** Tau-closure. *)
  Inductive tau_star : L.conf -> L.conf -> Prop :=
    | tau_star_refl : forall c, tau_star c c
    | tau_star_step : forall c c' c'',
        L.step c L.tau c' -> tau_star c' c'' -> tau_star c c''.

  (** tau_star is transitive.  Qed-closed by induction. *)
  Lemma tau_star_trans : forall c c' c'',
    tau_star c c' -> tau_star c' c'' -> tau_star c c''.
  Proof.
    intros c c' c'' H1 H2. induction H1.
    - exact H2.
    - eapply tau_star_step. eexact H. apply IHtau_star. exact H2.
  Qed.

  (** Up-to-tau function. *)
  Definition up_to_tau (R : L.conf -> L.conf -> Prop)
                       (c d : L.conf) : Prop :=
    exists c0 d0, tau_star c c0 /\ R c0 d0 /\ tau_star d0 d.

  (** The bisimulation functor (homogeneous case for clarity). *)
  Definition F (R : L.conf -> L.conf -> Prop)
               (c d : L.conf) : Prop :=
    forall a c',
      L.step c a c' ->
      exists d' d0, tau_star d d0 /\ L.step d0 a d' /\ R c' d'.

  (** [monotone_subset P Q] is [forall x y, P x y -> Q x y]. *)
  Definition monotone_subset (P Q : L.conf -> L.conf -> Prop) : Prop :=
    forall x y, P x y -> Q x y.

  (** up_to_tau is inflationary: R ⊆ up_to_tau R for every R.
      Qed-closed: take the reflexive tau-closure on both sides. *)
  Lemma up_to_tau_inflationary :
    forall R, monotone_subset R (up_to_tau R).
  Proof.
    intros R c d HR. unfold up_to_tau.
    exists c, d. split; [constructor|]. split; [exact HR|]. constructor.
  Qed.

  (** up_to_tau is monotone in its argument: R ⊆ S implies
      up_to_tau R ⊆ up_to_tau S. *)
  Lemma up_to_tau_monotone :
    forall R S,
      monotone_subset R S ->
      monotone_subset (up_to_tau R) (up_to_tau S).
  Proof.
    intros R S Hsub c d [c0 [d0 [Hc [HR Hd]]]].
    exists c0, d0. split; [exact Hc|].
    split; [apply Hsub; exact HR|]. exact Hd.
  Qed.

  (** up_to_tau absorbs tau_star on the left and the right:
      tau_star c c0 -> up_to_tau R c0 d -> up_to_tau R c d. *)
  Lemma up_to_tau_absorb_left :
    forall R c c0 d,
      tau_star c c0 -> up_to_tau R c0 d -> up_to_tau R c d.
  Proof.
    intros R c c0 d Hc [c1 [d1 [Hc0c1 [HR Hd]]]].
    exists c1, d1. split.
    - apply tau_star_trans with (c' := c0); assumption.
    - split; assumption.
  Qed.

  Lemma up_to_tau_absorb_right :
    forall R c d d0,
      tau_star d0 d -> up_to_tau R c d0 -> up_to_tau R c d.
  Proof.
    intros R c d d0 Hd [c1 [d1 [Hc [HR Hd0d1]]]].
    exists c1, d1. split; [exact Hc|].
    split; [exact HR|].
    apply tau_star_trans with (c' := d0); assumption.
  Qed.

  (** up_to_tau is idempotent: up_to_tau (up_to_tau R) = up_to_tau R
      (as a subset relation, both directions). *)
  Lemma up_to_tau_idempotent :
    forall R,
      monotone_subset (up_to_tau (up_to_tau R)) (up_to_tau R).
  Proof.
    intros R c d [c0 [d0 [Hc [[c1 [d1 [Hc0c1 [HR Hd1d0]]]] Hd]]]].
    exists c1, d1. split.
    - apply tau_star_trans with (c' := c0); assumption.
    - split; [exact HR|].
      apply tau_star_trans with (c' := d0); assumption.
  Qed.

  (** Step is deterministic up to tau_star: if step c tau c1 and
      step c tau c2, then c1 = c2 (by L.step_deterministic). *)
  Lemma tau_step_deterministic :
    forall c c1 c2,
      L.step c L.tau c1 -> L.step c L.tau c2 -> c1 = c2.
  Proof.
    intros c c1 c2 H1 H2.
    exact (L.step_deterministic H1 H2).
  Qed.

  (** The abstract measure strictly decreases along any tau_star
      chain of length at least one: tau_star c c' and c <> c'
      implies tau_measure c' < tau_measure c.  (Phrased
      contrapositively via the tau_decreases axiom for a single
      step; longer chains compose via transitivity.) *)
  Lemma tau_measure_strict_decrease :
    forall c c',
      L.step c L.tau c' -> L.tau_measure c' < L.tau_measure c.
  Proof.
    intros c c' H. exact (L.tau_decreases H).
  Qed.

  (** Compatibility statement. The Pous-Sangiorgi criterion. *)
  Definition compatible (f : (L.conf -> L.conf -> Prop) -> L.conf -> L.conf -> Prop) : Prop :=
    forall R, monotone_subset (f (F R)) (F (f R)).

  (** The up-to-tau compatibility theorem.
      Soundness via the Pous-Sangiorgi compatibility criterion.

      Status: the naive statement [compatible up_to_tau] as
      currently defined is FALSE under the present LTS axioms
      ({step_deterministic, tau_decreases}) without additional
      structure.

      Counterexample (verified with a compiled Coq instance):
      LTS with four states {s, t, d0, d} and action {tau, a}
      where  s --a--> t,  d0 --a--> t,  d0 --tau--> d,  d has
      no outgoing steps, tau_measure s=2, d0=1, d=t=0.  For
      R(x, y) := x = t /\ y = t, the relation [up_to_tau (F R) s d]
      holds (witness: c0 = s, d0 = d0, tau_star d0 d via the
      d0-tau-d step), but [F (up_to_tau R) s d] does not — d has
      no outgoing step to match the visible step [s --a--> t].

      Root cause: the current [up_to_tau] uses [tau_star d0 d]
      on the right (d0 ancestor of d) rather than [tau_star d d0]
      (d0 descendant of d).  The asymmetric closure lets the
      up-to side "look backwards" through tau-chains, which the
      functor F cannot match.  Fixing this requires replacing
      [tau_star d0 d] with [tau_star d d0] and adjusting F to
      use weak-step matching on both sides.

      The infrastructure lemmas above remain correct and Qed-closed
      — they are used by the replacement development in
      [UpToTauCorrected] below, which closes a corrected
      compatibility theorem with [Qed]. *)

  (** [up_to_tau_compatible] RETIRED: the statement [compatible
      up_to_tau] under the naive orientation is FALSE, mechanically
      refuted by [UpToTauCounterexample.up_to_tau_not_compatible]
      (a Qed-closed negative theorem over a concrete 4-state LTS).
      Do not reintroduce this theorem here — either use
      [UpToTauCorrected.up_to_tau_compatible_corrected] (Qed-closed
      under the correct orientation) or cite the counterexample
      file's refutation. *)

  Definition weak_bisim (R : L.conf -> L.conf -> Prop) : Prop :=
    monotone_subset R (F R).

  (** [up_to_tau_sound] RETIRED: soundness under the naive
      orientation would require the (false) compatibility theorem
      above as a lemma.  The corrected form is
      [UpToTauCorrected.up_to_tau_sound_corrected] (Qed-closed). *)

End UpToTau.

(** * Corrected up-to-tau development with the right orientation *)

(** Repairs the orientation of [up_to_tau] on the d-side:
    [tau_star d d0] (d0 reachable from d) rather than
    [tau_star d0 d] (d reachable from d0).  With this correction,
    compatibility holds for the up-to-tau closure under a functor
    that matches visible steps by weak transitions on both sides. *)
Module UpToTauCorrected (L : LTS).

  Inductive tau_star : L.conf -> L.conf -> Prop :=
    | tau_star_refl : forall c, tau_star c c
    | tau_star_step : forall c c' c'',
        L.step c L.tau c' -> tau_star c' c'' -> tau_star c c''.

  Lemma tau_star_trans : forall c c' c'',
    tau_star c c' -> tau_star c' c'' -> tau_star c c''.
  Proof.
    intros c c' c'' H1 H2. induction H1.
    - exact H2.
    - eapply tau_star_step. eexact H. apply IHtau_star. exact H2.
  Qed.

  (** Corrected up-to-tau: the c-side closes backwards so any weak
      step from [c] also starts from the witness [c0]; the d-side
      closes forwards so any weak match from [d0] can be replayed
      from [d]. *)
  Definition up_to_tau (R : L.conf -> L.conf -> Prop)
                       (c d : L.conf) : Prop :=
    exists c0 d0, tau_star c0 c /\ tau_star d d0 /\ R c0 d0.

  (** Weak visible step: tau_star prefix + step + tau_star suffix. *)
  Definition weak_step (c : L.conf) (a : L.obs) (c' : L.conf) : Prop :=
    exists c1 c2,
      tau_star c c1 /\ L.step c1 a c2 /\ tau_star c2 c'.

  (** Corrected functor: match weak steps by weak steps on the other
      side, leaving the continuation relation explicit. *)
  Definition F (R : L.conf -> L.conf -> Prop) (c d : L.conf) : Prop :=
    forall a c',
      weak_step c a c' ->
      exists d', weak_step d a d' /\ R c' d'.

  Definition monotone_subset (P Q : L.conf -> L.conf -> Prop) : Prop :=
    forall x y, P x y -> Q x y.

  Definition compatible (f : (L.conf -> L.conf -> Prop) -> L.conf -> L.conf -> Prop) : Prop :=
    forall R, monotone_subset (f (F R)) (F (f R)).

  Lemma up_to_tau_inflationary : forall R, monotone_subset R (up_to_tau R).
  Proof.
    intros R c d HR. exists c, d. split; [constructor|].
    split; [constructor|]. exact HR.
  Qed.

  Lemma up_to_tau_monotone :
    forall R S,
      monotone_subset R S ->
      monotone_subset (up_to_tau R) (up_to_tau S).
  Proof.
    intros R S Hsub c d [c0 [d0 [Hc [Hd HR]]]].
    exists c0, d0. repeat split; [exact Hc | exact Hd | apply Hsub; exact HR].
  Qed.

  Lemma up_to_tau_idempotent :
    forall R,
      monotone_subset (up_to_tau (up_to_tau R)) (up_to_tau R).
  Proof.
    intros R c d [c1 [d1 [Hc [Hd [c0 [d0 [Hc0 [Hd0 HR]]]]]]]].
    exists c0, d0. split.
    - eapply tau_star_trans; eauto.
    - split.
      + eapply tau_star_trans; eauto.
      + exact HR.
  Qed.

  Lemma step_weak_step : forall c a c',
    L.step c a c' -> weak_step c a c'.
  Proof.
    intros. exists c, c'. split; [constructor|].
    split; [exact H|constructor].
  Qed.

  Lemma weak_step_prepend_tau : forall c c0 a d,
    tau_star c c0 -> weak_step c0 a d -> weak_step c a d.
  Proof.
    intros c c0 a d Htau [c1 [c2 [H1 [Hstep H2]]]].
    exists c1, c2. split.
    - apply tau_star_trans with (c' := c0); assumption.
    - split; assumption.
  Qed.

  Lemma weak_step_append_tau : forall c a d d0,
    weak_step c a d -> tau_star d d0 -> weak_step c a d0.
  Proof.
    intros c a d d0 [c1 [c2 [H1 [Hstep H2]]]] Htau.
    exists c1, c2. split; [exact H1 | split; [exact Hstep|]].
    apply tau_star_trans with (c' := d); assumption.
  Qed.

  Lemma F_monotone :
    forall R S,
      monotone_subset R S ->
      monotone_subset (F R) (F S).
  Proof.
    intros R S Hsub c d HF a c' Hstep.
    destruct (HF a c' Hstep) as [d' [Hweak HR]].
    exists d'. split; [exact Hweak|].
    apply Hsub. exact HR.
  Qed.

  (** Corrected compatibility: the left witness [c0] sits before [c],
      so any weak step from [c] is also a weak step from [c0]; the
      right witness [d0] sits after [d], so a match from [d0] can be
      replayed from [d]. *)
  Theorem up_to_tau_compatible_corrected : compatible up_to_tau.
  Proof.
    intros R c d [c0 [d0 [Hc [Hd HF]]]].
    intros a c' Hstep.
    assert (Hstep0 : weak_step c0 a c').
    { eapply weak_step_prepend_tau; eauto. }
    destruct (HF a c' Hstep0) as [d' [Hweak HR]].
    exists d'. split.
    - eapply weak_step_prepend_tau; eauto.
    - exists c', d'. split; [constructor|].
      split; [constructor|exact HR].
  Qed.

  Definition weak_bisim (R : L.conf -> L.conf -> Prop) : Prop :=
    monotone_subset R (F R).

  Theorem up_to_tau_sound_corrected :
    forall R,
      monotone_subset R (F (up_to_tau R)) ->
      exists S, weak_bisim S /\ monotone_subset R S.
  Proof.
    intros R Hprog.
    exists (up_to_tau R). split.
    - unfold weak_bisim.
      intros c d HS.
      pose proof ((@up_to_tau_monotone R (F (up_to_tau R)) Hprog) c d HS) as Hlift.
      pose proof up_to_tau_compatible_corrected as Hcompat.
      unfold compatible in Hcompat.
      pose proof (Hcompat (up_to_tau R) c d Hlift) as Hclosure.
      exact ((@F_monotone (up_to_tau (up_to_tau R)) (up_to_tau R)
                (@up_to_tau_idempotent R)) c d Hclosure).
    - apply up_to_tau_inflationary.
  Qed.

End UpToTauCorrected.
