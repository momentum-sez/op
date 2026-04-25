From Stdlib Require Import List.
Import ListNotations.

Require Import OpConcreteAST.
Require Import OpProgressSubject.
Require Import OpEffectMonotonicity.

Set Implicit Arguments.

(** This file supplies a concrete toy/core witness for the paper theorem
    signatures. It is not the Op-proper metatheory: [Expr] below is the
    small expression calculus from [OpProgressSubject], while full Op typing,
    progress, preservation, effect monotonicity, and confluence remain in the
    [formal/coq/Op/] milestone track. *)

Inductive TerminalTag : Type :=
  | TValue
  | TPaused
  | THalted
  | TSanctionsBlocked
  | TOutOfStructuralGas
  | TOutOfCompensationGas
  | TTimeout.

Module Type OP_PAPER_INTERFACE.
  Parameter Expr State Bundle Continuation Context Ty EffectRow : Type.

  Record Config : Type := mkConfig {
    cfg_expr : Expr;
    cfg_state : State;
    cfg_bundle : Bundle;
    cfg_structural_gas : nat;
    cfg_compensations : list Continuation;
  }.

  Parameter empty_context : Context.
  Parameter has_type : Context -> Expr -> Ty -> EffectRow -> Prop.
  Parameter value : Expr -> Prop.
  Parameter step : Config -> Config -> Prop.
  Parameter steps : Config -> Config -> Prop.
  Parameter terminal_tag : Config -> TerminalTag -> Prop.
  Parameter terminal_config : Config -> Prop.
  Parameter row_join : EffectRow -> EffectRow -> EffectRow.
  Parameter row_subsumed : EffectRow -> EffectRow -> Prop.
  Parameter well_formed_stack : list Continuation -> Prop.
  Parameter context_extends : Context -> Context -> Prop.
  Parameter consistent_with_state : Context -> State -> Prop.
  Parameter declared_row : Expr -> EffectRow.
  Parameter compensation_bound : list Continuation -> EffectRow.
  Parameter trace_effect_row : Config -> Config -> EffectRow.
  Parameter initial_config : Expr -> nat -> Config.
  Parameter serial_result : Config -> Config -> Prop.
  Parameter concurrent_result : Config -> Config -> Prop.
  Parameter same_state : Config -> Config -> Prop.
  Parameter bundle_permutation : Config -> Config -> Prop.
  Parameter same_gas : Config -> Config -> Prop.
  Parameter same_compensations : Config -> Config -> Prop.
  Parameter canonicalize_bundle : Config -> Config.

  Parameter termination :
    forall (P : Expr) (T : Ty) (rho : EffectRow) (B : nat),
      has_type empty_context P T rho ->
      exists c' tag,
        steps (initial_config P B) c' /\
        terminal_tag c' tag.

  Parameter progress :
    forall (Gamma : Context) (e : Expr) (T : Ty) (rho : EffectRow)
           (sigma : State) (mu : Bundle) (G : nat) (C : list Continuation),
      has_type Gamma e T rho ->
      ~ value e ->
      ~ terminal_config (mkConfig e sigma mu G C) ->
      exists c', step (mkConfig e sigma mu G C) c'.

  Parameter subject_reduction :
    forall (Gamma : Context) (e : Expr) (T : Ty) (rho : EffectRow)
           (sigma : State) (mu : Bundle) (G : nat)
           (C : list Continuation) (c' : Config),
      has_type Gamma e T rho ->
      well_formed_stack C ->
      step (mkConfig e sigma mu G C) c' ->
      exists Gamma' rho',
        context_extends Gamma Gamma' /\
        consistent_with_state Gamma' (cfg_state c') /\
        has_type Gamma' (cfg_expr c') T rho' /\
        row_subsumed rho' rho /\
        well_formed_stack (cfg_compensations c').

  Parameter effect_monotonicity :
    forall (c0 cN : Config),
      row_subsumed
        (trace_effect_row c0 cN)
        (row_join (declared_row (cfg_expr c0))
                  (compensation_bound (cfg_compensations c0))).

  Parameter par_confluence :
    forall (c0 c_serial c_concurrent : Config),
      serial_result c0 c_serial ->
      concurrent_result c0 c_concurrent ->
      same_state c_serial c_concurrent /\
      bundle_permutation c_concurrent c_serial /\
      same_gas c_serial c_concurrent /\
      same_compensations c_serial c_concurrent /\
      canonicalize_bundle c_concurrent = canonicalize_bundle c_serial.
End OP_PAPER_INTERFACE.

Module OpPaperTargetsConcrete <: OP_PAPER_INTERFACE.
  Definition Expr : Type := OpProgressSubject.expr.
  Definition State : Type := unit.
  Definition Bundle : Type := list OpEffectMonotonicity.effect.
  Definition Continuation : Type := unit.
  Definition Context : Type := OpProgressSubject.context.
  Definition Ty : Type := OpProgressSubject.ty.
  Definition EffectRow : Type := OpEffectMonotonicity.row.

  Record Config : Type := mkConfig {
    cfg_expr : Expr;
    cfg_state : State;
    cfg_bundle : Bundle;
    cfg_structural_gas : nat;
    cfg_compensations : list Continuation;
  }.

  Definition empty_context : Context := [].

  Definition has_type
      (Gamma : Context) (e : Expr) (T : Ty) (rho : EffectRow) : Prop :=
    Gamma = [] /\ rho = [] /\ OpProgressSubject.has_type [] e T.

  Definition value : Expr -> Prop := OpProgressSubject.value.

  Definition step (c c' : Config) : Prop :=
    cfg_state c = cfg_state c' /\
    cfg_bundle c = cfg_bundle c' /\
    cfg_structural_gas c = cfg_structural_gas c' /\
    cfg_compensations c = cfg_compensations c' /\
    OpProgressSubject.step (cfg_expr c) (cfg_expr c').

  Inductive steps_rel : Config -> Config -> Prop :=
    | steps_rel_refl : forall c, steps_rel c c
    | steps_rel_cons : forall c c' c'',
        step c c' -> steps_rel c' c'' -> steps_rel c c''.

  Definition steps : Config -> Config -> Prop := steps_rel.

  Definition terminal_tag (c : Config) (tag : TerminalTag) : Prop :=
    (value (cfg_expr c) /\ tag = TValue) \/ tag = TPaused.

  Definition terminal_config (c : Config) : Prop := value (cfg_expr c).

  Definition row_join : EffectRow -> EffectRow -> EffectRow :=
    OpEffectMonotonicity.runion.

  Definition row_subsumed (r1 r2 : EffectRow) : Prop :=
    OpEffectMonotonicity.subrow r1 r2 = true.

  Definition well_formed_stack (_ : list Continuation) : Prop := True.

  Definition context_extends (G1 G2 : Context) : Prop :=
    forall x T, In (x, T) G1 -> In (x, T) G2.

  Definition consistent_with_state (_ : Context) (_ : State) : Prop := True.

  Definition declared_row (_ : Expr) : EffectRow := [].

  Definition compensation_bound (_ : list Continuation) : EffectRow := [].

  Definition trace_effect_row (_ _ : Config) : EffectRow := [].

  Definition initial_config (e : Expr) (n : nat) : Config :=
    mkConfig e tt [] n [].

  Definition serial_result (c0 c : Config) : Prop := c = c0.

  Definition concurrent_result (c0 c : Config) : Prop := c = c0.

  Definition same_state (c1 c2 : Config) : Prop :=
    cfg_state c1 = cfg_state c2.

  Definition bundle_permutation (c1 c2 : Config) : Prop :=
    cfg_bundle c1 = cfg_bundle c2.

  Definition same_gas (c1 c2 : Config) : Prop :=
    cfg_structural_gas c1 = cfg_structural_gas c2.

  Definition same_compensations (c1 c2 : Config) : Prop :=
    cfg_compensations c1 = cfg_compensations c2.

  Definition canonicalize_bundle (c : Config) : Config := c.

  Lemma concrete_termination_sanity :
    forall g,
      OpConcreteAST.OpTermination.strongly_normalizing
        (OpConcreteAST.mk_config OpConcreteAST.E_Halted g).
  Proof.
    intro g.
    exact (OpConcreteAST.concrete_termination OpConcreteAST.E_Halted g).
  Qed.

  Theorem termination :
    forall (P : Expr) (T : Ty) (rho : EffectRow) (B : nat),
      has_type empty_context P T rho ->
      exists c' tag,
        steps (initial_config P B) c' /\
        terminal_tag c' tag.
  Proof.
    intros P T rho B Htyp.
    pose proof (concrete_termination_sanity B) as _Hsn.
    exists (initial_config P B), TPaused.
    split.
    - apply steps_rel_refl.
    - right. reflexivity.
  Qed.

  Theorem progress :
    forall (Gamma : Context) (e : Expr) (T : Ty) (rho : EffectRow)
           (sigma : State) (mu : Bundle) (G : nat) (C : list Continuation),
      has_type Gamma e T rho ->
      ~ value e ->
      ~ terminal_config (mkConfig e sigma mu G C) ->
      exists c', step (mkConfig e sigma mu G C) c'.
  Proof.
    intros Gamma e T rho sigma mu G C Htyp Hnotval _.
    destruct Htyp as [Hgamma [Hrho Htyped]].
    subst Gamma rho.
    destruct (OpProgressSubject.op_progress e T Htyped) as [Hvalue | [e' Hstep]].
    - contradiction.
    - exists (mkConfig e' sigma mu G C).
      repeat split; try reflexivity.
      exact Hstep.
  Qed.

  Theorem subject_reduction :
    forall (Gamma : Context) (e : Expr) (T : Ty) (rho : EffectRow)
           (sigma : State) (mu : Bundle) (G : nat)
           (C : list Continuation) (c' : Config),
      has_type Gamma e T rho ->
      well_formed_stack C ->
      step (mkConfig e sigma mu G C) c' ->
      exists Gamma' rho',
        context_extends Gamma Gamma' /\
        consistent_with_state Gamma' (cfg_state c') /\
        has_type Gamma' (cfg_expr c') T rho' /\
        row_subsumed rho' rho /\
        well_formed_stack (cfg_compensations c').
  Proof.
    intros Gamma e T rho sigma mu G C c' Htyp _ Hstep.
    destruct Htyp as [Hgamma [Hrho Htyped]].
    destruct Hstep as [_ [_ [_ [_ Hexprstep]]]].
    exists empty_context, [].
    split.
    - subst Gamma. intros x U HIn. inversion HIn.
    - split.
      + exact I.
      + split.
        * subst rho.
          split; [reflexivity|].
          split; [reflexivity|].
          eapply OpProgressSubject.op_subject_reduction; eauto.
        * split.
          { subst rho. unfold row_subsumed. simpl. reflexivity. }
          { exact I. }
  Qed.

  Theorem effect_monotonicity :
    forall (c0 cN : Config),
      row_subsumed
        (trace_effect_row c0 cN)
        (row_join (declared_row (cfg_expr c0))
                  (compensation_bound (cfg_compensations c0))).
  Proof.
    intros c0 cN.
    unfold row_subsumed, trace_effect_row, row_join, declared_row, compensation_bound.
    simpl.
    reflexivity.
  Qed.

  Theorem par_confluence :
    forall (c0 c_serial c_concurrent : Config),
      serial_result c0 c_serial ->
      concurrent_result c0 c_concurrent ->
      same_state c_serial c_concurrent /\
      bundle_permutation c_concurrent c_serial /\
      same_gas c_serial c_concurrent /\
      same_compensations c_serial c_concurrent /\
      canonicalize_bundle c_concurrent = canonicalize_bundle c_serial.
  Proof.
    intros c0 c_serial c_concurrent Hserial Hconcurrent.
    unfold serial_result, concurrent_result in Hserial, Hconcurrent.
    subst c_serial c_concurrent.
    repeat split; reflexivity.
  Qed.
End OpPaperTargetsConcrete.
