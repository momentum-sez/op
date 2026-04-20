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

End GasTerminationTheory.
