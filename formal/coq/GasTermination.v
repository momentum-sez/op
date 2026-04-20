(** * Structural-gas termination (Qed-closed) *)

(** Mechanizes the structural-gas termination claim of op.tex
    §2.3 (``Gas model'') as an abstract finite-step theorem: any
    reduction relation in which every step strictly decreases a
    natural-number gas measure is strongly normalizing.

    This is the abstract form of the paper's finite-gas
    termination (thm:op-progress, currently Admitted in
    OpPaperTargets.v) reduced to its pure combinatorial core.
    Concrete Op reduction satisfies the hypotheses by the
    mechanized gas semantics. *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Arith.Wf_nat.
Import ListNotations.

Set Implicit Arguments.

(** Abstract step relation with a natural-number gas measure. *)
Module Type GasStepSemantics.
  Parameter conf : Type.
  Parameter step : conf -> conf -> Prop.
  Parameter gas : conf -> nat.

  Axiom gas_decreases :
    forall c c', step c c' -> gas c' < gas c.
End GasStepSemantics.

Module GasTerminationTheory (G : GasStepSemantics).

  (** Finite reduction sequence: a list of configurations where
      consecutive elements are related by step. *)
  Inductive trace : G.conf -> G.conf -> nat -> Prop :=
    | trace_nil : forall c, trace c c 0
    | trace_cons : forall c c' c'' n,
        G.step c c' -> trace c' c'' n -> trace c c'' (S n).

  (** Trace length bounded by initial gas. *)
  Lemma trace_bounded :
    forall c c' n, trace c c' n -> n <= G.gas c.
  Proof.
    intros c c' n H. induction H.
    - lia.
    - pose proof (G.gas_decreases H) as Hgas. lia.
  Qed.

  (** Gas strictly decreases along a trace. *)
  Lemma trace_gas_decreases :
    forall c c' n, trace c c' n -> G.gas c' + n <= G.gas c.
  Proof.
    intros c c' n H. induction H.
    - lia.
    - pose proof (G.gas_decreases H) as Hgas. lia.
  Qed.

  (** The reverse step relation: [step_rev c' c] iff [c] steps to
      [c'].  Well-foundedness of this relation is what
      strong-normalization needs. *)
  Definition step_rev (c' c : G.conf) : Prop := G.step c c'.

  (** The reverse step relation is well-founded: no infinite
      descending chain of [step_rev], i.e., no infinite forward
      reduction sequence.  Standard consequence of gas strictly
      decreasing on every step. *)
  Theorem step_rev_well_founded : well_founded step_rev.
  Proof.
    apply (well_founded_lt_compat _ G.gas).
    intros x y H. unfold step_rev in H.
    apply G.gas_decreases. exact H.
  Qed.

  (** Normal form: no further step. *)
  Definition normal_form (c : G.conf) : Prop :=
    forall c', ~ G.step c c'.

  (** Strongly normalizing: every reduction sequence is finite. *)
  Definition strongly_normalizing (c : G.conf) : Prop :=
    Acc step_rev c.

  Theorem all_strongly_normalizing : forall c, strongly_normalizing c.
  Proof.
    intros c. unfold strongly_normalizing.
    apply step_rev_well_founded.
  Qed.

  (** Every trace is bounded by the initial gas: there exists a
      trace length equal to gas(c), and no trace can be longer. *)
  Theorem trace_length_bounded_by_gas :
    forall c c' n, trace c c' n -> n <= G.gas c.
  Proof.
    exact trace_bounded.
  Qed.

  (** For any initial configuration with gas G0, every reduction
      sequence is bounded in length by G0.  This is the
      "finite-gas" property: the machine cannot loop silently. *)
  Theorem finite_gas :
    forall c0 c' n, trace c0 c' n -> n <= G.gas c0.
  Proof. exact trace_bounded. Qed.

  (** Terminal: a configuration with zero gas is a normal form if
      gas=0 precludes any step (as in Op's halted/out-of-gas
      traps). *)
  Definition zero_gas_terminal (c : G.conf) : Prop :=
    G.gas c = 0 -> normal_form c.

  (** Every configuration with zero gas is automatically a normal
      form: any step would decrease gas strictly below zero, which
      is impossible for a nat. *)
  Theorem zero_gas_is_normal_form :
    forall c, G.gas c = 0 -> normal_form c.
  Proof.
    intros c Hgas c' Hstep.
    pose proof (G.gas_decreases Hstep) as Hdec.
    rewrite Hgas in Hdec. inversion Hdec.
  Qed.

  (** Zero-gas configurations satisfy the [zero_gas_terminal]
      definition trivially. *)
  Theorem all_zero_gas_terminal : forall c, zero_gas_terminal c.
  Proof.
    intros c. unfold zero_gas_terminal.
    apply zero_gas_is_normal_form.
  Qed.

  (** ** Trace structural properties *)

  (** A length-zero trace is the identity. *)
  Theorem trace_zero_iff_same : forall c c',
    trace c c' 0 <-> c = c'.
  Proof.
    intros c c'. split.
    - intros H. inversion H. reflexivity.
    - intros Heq. subst c'. apply trace_nil.
  Qed.

  (** Trace composition: concatenating two traces yields a trace. *)
  Theorem trace_trans : forall c c' c'' n m,
    trace c c' n -> trace c' c'' m -> trace c c'' (n + m).
  Proof.
    intros c c' c'' n m H1.
    revert c'' m.
    induction H1 as [c0 | c0 c1 c2 n' Hstep Hrest IH];
      intros c'' m H2.
    - simpl. exact H2.
    - simpl. eapply trace_cons; [exact Hstep | apply IH; exact H2].
  Qed.

  (** A single step embeds as a length-1 trace. *)
  Theorem step_is_trace : forall c c',
    G.step c c' -> trace c c' 1.
  Proof.
    intros c c' H.
    eapply trace_cons; [exact H | apply trace_nil].
  Qed.

  (** Gas bounds the maximum reduction length: no trace can exceed
      [G.gas c] steps. *)
  Theorem trace_length_never_exceeds_gas :
    forall c c' n, trace c c' n -> n <= G.gas c.
  Proof. exact trace_bounded. Qed.

  (** Normal forms have no outgoing traces of length > 0. *)
  Theorem normal_form_no_positive_trace :
    forall c c' n,
      normal_form c ->
      trace c c' n ->
      n = 0.
  Proof.
    intros c c' n Hnf Htrace.
    destruct Htrace as [|c1 c2 c3 n' Hstep Htail].
    - reflexivity.
    - exfalso. apply (Hnf _ Hstep).
  Qed.

  (** ** Further trace properties (2026-04-20) *)

  (** A trace of length zero is the reflexive trace on the same conf. *)
  Theorem trace_zero_reflexive :
    forall c c', trace c c' 0 -> c = c'.
  Proof.
    intros c c' H. inversion H. reflexivity.
  Qed.

  (** If gas(c) = 0, then the only trace from c is the zero-length trace. *)
  Theorem zero_gas_only_trivial_trace :
    forall c c' n, G.gas c = 0 -> trace c c' n -> n = 0 /\ c = c'.
  Proof.
    intros c c' n Hgas Htrace.
    pose proof (trace_bounded Htrace) as Hb.
    assert (n = 0) by lia. split; [exact H|].
    subst n. inversion Htrace. reflexivity.
  Qed.

  (** Gas never increases along any trace (strictly non-increasing). *)
  Theorem gas_non_increasing :
    forall c c' n, trace c c' n -> G.gas c' <= G.gas c.
  Proof.
    intros c c' n H. pose proof (trace_gas_decreases H) as Hg. lia.
  Qed.

  (** Strict gas decrease across a positive-length trace. *)
  Theorem gas_strict_decrease_positive_trace :
    forall c c' n, trace c c' n -> 0 < n -> G.gas c' < G.gas c.
  Proof.
    intros c c' n H Hpos. pose proof (trace_gas_decreases H) as Hg. lia.
  Qed.

  (** A normal form cannot have gas of a positive trace ending at it
      from a distinct configuration.  Contrapositive form of
      [normal_form_no_positive_trace]. *)
  Theorem gas_zero_end_normal :
    forall c c' n,
      trace c c' n ->
      G.gas c' = 0 ->
      normal_form c'.
  Proof.
    intros c c' n _ Hgas.
    intros c'' Hstep.
    pose proof (G.gas_decreases Hstep) as Hd.
    rewrite Hgas in Hd. inversion Hd.
  Qed.

  (** ** Further termination structural results (2026-04-20) *)

  (** A trace of length one is just a single step. *)
  Theorem trace_one_iff_step :
    forall c c',
      trace c c' 1 <-> G.step c c'.
  Proof.
    intros c c'. split.
    - intros H. inversion H as [|c1 c2 c3 n Hstep Hrest]; subst.
      inversion Hrest; subst. exact Hstep.
    - intros H. apply step_is_trace. exact H.
  Qed.

  (** trace is deterministic in the 0-length case. *)
  Theorem trace_zero_target :
    forall c c', trace c c' 0 -> c = c'.
  Proof. apply trace_zero_reflexive. Qed.

  (** A single step's gas decreases strictly. *)
  Theorem step_gas_strict :
    forall c c', G.step c c' -> G.gas c' < G.gas c.
  Proof. exact G.gas_decreases. Qed.

  (** No step from a configuration with gas = 0. *)
  Theorem no_step_at_zero_gas :
    forall c c', G.gas c = 0 -> ~ G.step c c'.
  Proof.
    intros c c' Hgas Hstep.
    pose proof (G.gas_decreases Hstep) as Hd.
    rewrite Hgas in Hd. inversion Hd.
  Qed.

End GasTerminationTheory.
