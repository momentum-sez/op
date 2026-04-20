From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Wellfounded.Wellfounded.

Import ListNotations.

Set Implicit Arguments.

Module Type GasStepSemantics.
  Parameter conf : Type.
  Parameter step : conf -> conf -> Prop.
  Parameter gas : conf -> nat.

  Axiom gas_decreases :
    forall c c', step c c' -> gas c' < gas c.
End GasStepSemantics.

Module GasTerminationTheory (G : GasStepSemantics).

  Inductive trace : G.conf -> G.conf -> nat -> Prop :=
    | trace_nil : forall c, trace c c 0
    | trace_cons : forall c c' c'' n,
        G.step c c' -> trace c' c'' n -> trace c c'' (S n).

  Lemma trace_bounded :
    forall c c' n, trace c c' n -> n <= G.gas c.
  Proof.
    intros c c' n H. induction H.
    - lia.
    - pose proof (G.gas_decreases H) as Hgas. lia.
  Qed.

  Lemma trace_gas_decreases :
    forall c c' n, trace c c' n -> G.gas c' + n <= G.gas c.
  Proof.
    intros c c' n H. induction H.
    - lia.
    - pose proof (G.gas_decreases H) as Hgas. lia.
  Qed.

  Definition step_rev (c' c : G.conf) : Prop := G.step c c'.

  Theorem step_rev_well_founded : well_founded step_rev.
  Proof.
    apply (well_founded_lt_compat _ G.gas).
    intros x y H. unfold step_rev in H.
    apply G.gas_decreases. exact H.
  Qed.

  Definition normal_form (c : G.conf) : Prop :=
    forall c', ~ G.step c c'.

  Definition strongly_normalizing (c : G.conf) : Prop :=
    Acc step_rev c.

  Theorem all_strongly_normalizing : forall c, strongly_normalizing c.
  Proof.
    intros c. unfold strongly_normalizing.
    apply step_rev_well_founded.
  Qed.

  Theorem trace_length_bounded_by_gas :
    forall c c' n, trace c c' n -> n <= G.gas c.
  Proof.
    exact trace_bounded.
  Qed.

  Theorem finite_gas :
    forall c0 c' n, trace c0 c' n -> n <= G.gas c0.
  Proof.
    exact trace_bounded.
  Qed.

  Definition zero_gas_terminal (c : G.conf) : Prop :=
    G.gas c = 0 -> normal_form c.
End GasTerminationTheory.

Inductive expr : Type :=
  | E_Const : nat -> expr
  | E_Var : nat -> expr
  | E_Let : nat -> expr -> expr -> expr
  | E_App : expr -> expr -> expr
  | E_Lam : nat -> expr -> expr
  | E_Sanctions : expr -> expr
  | E_Halted : expr
  | E_SanctionsBlocked : expr
  | E_OutOfGas : expr.

Record config : Type := mk_config {
  cfg_expr : expr;
  cfg_gas : nat;
}.

Definition terminal_expr (e : expr) : Prop :=
  match e with
  | E_Halted => True
  | E_SanctionsBlocked => True
  | E_OutOfGas => True
  | _ => False
  end.

Definition non_terminal_expr (e : expr) : Prop := ~ terminal_expr e.

Definition reduce_expr (e : expr) : expr :=
  match e with
  | E_Const _ => E_Halted
  | E_Var _ => E_Halted
  | E_Let _ _ e2 => e2
  | E_App _ _ => E_Halted
  | E_Lam _ _ => E_Halted
  | E_Sanctions _ => E_SanctionsBlocked
  | E_Halted => E_Halted
  | E_SanctionsBlocked => E_SanctionsBlocked
  | E_OutOfGas => E_OutOfGas
  end.

Inductive step : config -> config -> Prop :=
  | Step_tick :
      forall e g,
        non_terminal_expr e ->
        step (mk_config e (S g)) (mk_config (reduce_expr e) g).

Definition gas (c : config) : nat := cfg_gas c.

Theorem gas_decreases : forall c c', step c c' -> gas c' < gas c.
Proof.
  intros c c' Hstep.
  inversion Hstep; subst; simpl; lia.
Qed.

Definition concrete_step := step.
Definition concrete_gas := gas.

Theorem concrete_gas_decreases :
  forall c c', concrete_step c c' -> concrete_gas c' < concrete_gas c.
Proof.
  exact gas_decreases.
Qed.

Module OpGasSemantics <: GasStepSemantics.
  Definition conf := config.
  Definition step := concrete_step.
  Definition gas := concrete_gas.

  Theorem gas_decreases : forall c c', step c c' -> gas c' < gas c.
  Proof.
    exact concrete_gas_decreases.
  Qed.
End OpGasSemantics.

Module OpTermination := GasTerminationTheory OpGasSemantics.

Corollary concrete_termination :
  forall e g, OpTermination.strongly_normalizing (mk_config e g).
Proof.
  intros e g.
  apply OpTermination.all_strongly_normalizing.
Qed.
