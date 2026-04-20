From Stdlib Require Import List.
Import ListNotations.

(** * OpPaperTargets.v

    Statement-level Rocq targets for the paper theorems in [papers/op.tex]
    that remain open.  The goal is to give each paper theorem a stable
    name and signature without overstating proof status. *)

Set Implicit Arguments.

Inductive TerminalTag : Type :=
  | TValue
  | TPaused
  | THalted
  | TSanctionsBlocked
  | TOutOfStructuralGas
  | TOutOfCompensationGas
  | TTimeout.

Section PaperTargets.
  Context {Expr State Bundle Continuation Context Ty EffectRow : Type}.

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

  Theorem termination :
    forall (P : Expr) (T : Ty) (rho : EffectRow) (B : nat),
      has_type empty_context P T rho ->
      exists c' tag,
        steps (initial_config P B) c' /\
        terminal_tag c' tag.
  Admitted.

  Theorem progress :
    forall (Gamma : Context) (e : Expr) (T : Ty) (rho : EffectRow)
           (sigma : State) (mu : Bundle) (G : nat) (C : list Continuation),
      has_type Gamma e T rho ->
      ~ value e ->
      ~ terminal_config (mkConfig e sigma mu G C) ->
      exists c', step (mkConfig e sigma mu G C) c'.
  Admitted.

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
  Admitted.

  Theorem effect_monotonicity :
    forall (c0 cN : Config),
      row_subsumed
        (trace_effect_row c0 cN)
        (row_join (declared_row (cfg_expr c0))
                  (compensation_bound (cfg_compensations c0))).
  Admitted.

  Theorem par_confluence :
    forall (c0 c_serial c_concurrent : Config),
      serial_result c0 c_serial ->
      concurrent_result c0 c_concurrent ->
      same_state c_serial c_concurrent /\
      bundle_permutation c_concurrent c_serial /\
      same_gas c_serial c_concurrent /\
      same_compensations c_serial c_concurrent /\
      canonicalize_bundle c_concurrent = canonicalize_bundle c_serial.
  Admitted.
End PaperTargets.
