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

  (** The 5 paper theorems (termination, progress, subject_reduction,
      effect_monotonicity, par_confluence) were previously [Admitted]
      here under abstract Parameters, which meant they were axiomatic
      stubs rather than proofs.

      They are now superseded at the signature-witness level by:

      - [OpPaperTargetsModuleType.v]: Module Type + concrete Module
        [OpPaperTargetsConcrete] instantiating each abstract Parameter
        with a concrete toy/core definition drawn from the Op AST files
        (OpConcreteAST, OpProgressSubject, OpEffectMonotonicity) and
        closing each of the 5 theorems with [Qed].

      - [OpPaperTargetsInstance.v]: direct exact-citation of the
        concrete theorems [concrete_termination] (from OpConcreteAST),
        [op_progress] / [op_subject_reduction] (from OpProgressSubject),
        [op_effect_monotonicity_empty_start] and
        [par_confluence_diamond] (from OpEffectMonotonicity), all Qed.

      These witnesses prove that the theorem signatures are consistent;
      they are not yet proofs of the paper theorems for Op proper. The
      Op-proper closure remains tied to the [formal/coq/Op/] typing,
      progress, preservation, and effect-semantics milestones.

      This file retains the parametric-interface section (Config,
      abstract Parameters, TerminalTag) as documentation of the
      paper-level signature shape, but no longer contains Admitted
      Theorems. *)
End PaperTargets.
