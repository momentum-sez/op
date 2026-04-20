(** * UpToTauCounterexample.v

    A compiled counterexample showing that the original
    [UpToTauCompatibility.UpToTau.up_to_tau] is not compatible with
    the functor [F] under the current abstract LTS axioms. *)

From Stdlib Require Import Lia.
Require Import UpToTauCompatibility.

Set Implicit Arguments.

Module CounterexampleLTS.

  Inductive state : Type :=
    | Ss
    | St
    | Sd0
    | Sd.

  Inductive action : Type :=
    | AA
    | Atau.

  Definition tau : action := Atau.

  Inductive step : state -> action -> state -> Prop :=
    | step_s_a : step Ss AA St
    | step_d0_a : step Sd0 AA St
    | step_d0_tau : step Sd0 Atau Sd.

  Definition tau_measure (c : state) : nat :=
    match c with
    | Ss => 2
    | Sd0 => 1
    | St => 0
    | Sd => 0
    end.

End CounterexampleLTS.

Module Counterex <: UpToTauCompatibility.LTS.

  Definition conf := CounterexampleLTS.state.
  Definition obs := CounterexampleLTS.action.
  Definition tau := CounterexampleLTS.tau.
  Definition step := CounterexampleLTS.step.

  Theorem step_deterministic :
    forall c a c1 c2,
      step c a c1 -> step c a c2 -> c1 = c2.
  Proof.
    intros c a c1 c2 H1 H2.
    inversion H1; inversion H2; subst; try reflexivity; congruence.
  Qed.

  Definition tau_measure := CounterexampleLTS.tau_measure.

  Theorem tau_decreases :
    forall c c', step c tau c' -> tau_measure c' < tau_measure c.
  Proof.
    intros c c' Hstep.
    inversion Hstep; subst; simpl; lia.
  Qed.

End Counterex.

Module UpToTauCounterex := UpToTauCompatibility.UpToTau Counterex.

Import CounterexampleLTS.
Import UpToTauCounterex.

Definition R : Counterex.conf -> Counterex.conf -> Prop :=
  fun x y => x = St /\ y = St.

Lemma tau_star_d0_d : tau_star Sd0 Sd.
Proof.
  eapply tau_star_step.
  - exact step_d0_tau.
  - apply tau_star_refl.
Qed.

Lemma step_from_Sd_absurd : forall a c, ~ Counterex.step Sd a c.
Proof.
  intros a c Hstep.
  inversion Hstep.
Qed.

Lemma tau_star_d_only : forall c, tau_star Sd c -> c = Sd.
Proof.
  intros c Htau.
  remember Sd as s eqn:Hs.
  induction Htau; subst.
  - reflexivity.
  - exfalso.
    eapply step_from_Sd_absurd.
    exact H.
Qed.

Lemma up_to_tau_F_R_Ss_Sd : up_to_tau (F R) Ss Sd.
Proof.
  unfold up_to_tau, F, R.
  exists Ss, Sd0.
  split.
  - apply tau_star_refl.
  - split.
    + intros a c' Hstep.
      inversion Hstep; subst.
      exists St, Sd0.
      split.
      * apply tau_star_refl.
      * split.
        -- exact step_d0_a.
        -- split; reflexivity.
    + exact tau_star_d0_d.
Qed.

Lemma F_up_to_tau_R_Ss_Sd_fails : ~ F (up_to_tau R) Ss Sd.
Proof.
  unfold F.
  intro HF.
  specialize (HF AA St step_s_a) as [d' [d0 [Htau [Hstep _]]]].
  pose proof (tau_star_d_only Htau) as ->.
  eapply step_from_Sd_absurd.
  exact Hstep.
Qed.

Theorem up_to_tau_not_compatible : ~ compatible up_to_tau.
Proof.
  intro Hcompat.
  unfold compatible, monotone_subset in Hcompat.
  pose proof (Hcompat R Ss Sd up_to_tau_F_R_Ss_Sd) as HF.
  exact (F_up_to_tau_R_Ss_Sd_fails HF).
Qed.

(** * Further counterexample-state properties (2026-04-20) *)

(** The four counterexample states are all distinct. *)
Theorem counterex_states_distinct :
  Ss <> St /\ Ss <> Sd0 /\ Ss <> Sd /\
  St <> Sd0 /\ St <> Sd /\ Sd0 <> Sd.
Proof. repeat split; discriminate. Qed.

(** tau_measure is strict-monotone along a step. *)
Theorem counterex_tau_measure_bounded :
  forall c, CounterexampleLTS.tau_measure c <= 2.
Proof.
  intros c. destruct c; simpl; lia.
Qed.

(** St is a dead-end: no outgoing steps. *)
Theorem St_no_step : forall a c, ~ Counterex.step St a c.
Proof. intros a c H. inversion H. Qed.

(** Ss has only one outgoing step (to St at action AA). *)
Theorem Ss_unique_step :
  forall a c, Counterex.step Ss a c -> a = AA /\ c = St.
Proof.
  intros a c H. inversion H; subst. split; reflexivity.
Qed.

(** Sd0 has exactly two outgoing steps. *)
Theorem Sd0_two_steps :
  forall a c,
    Counterex.step Sd0 a c ->
    (a = AA /\ c = St) \/ (a = Atau /\ c = Sd).
Proof.
  intros a c H. inversion H; subst.
  - left. split; reflexivity.
  - right. split; reflexivity.
Qed.

(** ** Further counterexample properties (2026-04-20) *)

(** Counterexample states have decidable equality. *)
Theorem counterex_state_eq_dec :
  forall s1 s2 : state, {s1 = s2} + {s1 <> s2}.
Proof. decide equality. Qed.

(** Counterexample actions have decidable equality. *)
Theorem counterex_action_eq_dec :
  forall a1 a2 : action, {a1 = a2} + {a1 <> a2}.
Proof. decide equality. Qed.

(** tau_measure is exactly 0 at both St and Sd. *)
Theorem counterex_tau_measure_zero_at_sinks :
  CounterexampleLTS.tau_measure St = 0 /\
  CounterexampleLTS.tau_measure Sd = 0.
Proof. split; reflexivity. Qed.

(** Ss has the maximum tau_measure (2) and is the only state at 2. *)
Theorem counterex_tau_measure_Ss :
  CounterexampleLTS.tau_measure Ss = 2.
Proof. reflexivity. Qed.

(** Sd0 sits strictly between Ss and the sinks. *)
Theorem counterex_tau_measure_Sd0 :
  CounterexampleLTS.tau_measure Sd0 = 1.
Proof. reflexivity. Qed.
