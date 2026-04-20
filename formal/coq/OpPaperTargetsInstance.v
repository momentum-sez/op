From Stdlib Require Import List.
Import ListNotations.
Require Import OpConcreteAST.
Require Import OpProgressSubject.
Require Import OpEffectMonotonicity.

Theorem termination_concrete :
  forall (e : OpConcreteAST.expr) (g : nat),
    exists c' : OpConcreteAST.config,
      OpConcreteAST.OpTermination.trace (OpConcreteAST.mk_config e g) c' 0 /\
      OpConcreteAST.OpTermination.strongly_normalizing c'.
Proof.
  intros e g.
  exists (OpConcreteAST.mk_config e g).
  split.
  - apply OpConcreteAST.OpTermination.trace_nil.
  - exact (OpConcreteAST.concrete_termination e g).
Qed.

Theorem progress_concrete :
  forall (e : OpProgressSubject.expr) (T : OpProgressSubject.ty),
    OpProgressSubject.has_type [] e T ->
    OpProgressSubject.value e \/ exists e', OpProgressSubject.step e e'.
Proof.
  exact OpProgressSubject.op_progress.
Qed.

Theorem subject_reduction_concrete :
  forall (G : OpProgressSubject.context)
         (e : OpProgressSubject.expr)
         (T : OpProgressSubject.ty)
         (e' : OpProgressSubject.expr),
    OpProgressSubject.has_type G e T ->
    OpProgressSubject.step e e' ->
    OpProgressSubject.has_type G e' T.
Proof.
  exact OpProgressSubject.op_subject_reduction.
Qed.

Theorem effect_monotonicity_concrete :
  forall (c0 cN : OpEffectMonotonicity.config),
    OpEffectMonotonicity.cfg_row c0 = [] ->
    OpEffectMonotonicity.multi_step c0 cN ->
    OpEffectMonotonicity.subrow
      (OpEffectMonotonicity.cfg_row cN)
      (OpEffectMonotonicity.runion
         (OpEffectMonotonicity.cfg_decl c0)
         (OpEffectMonotonicity.compensation_bound
            (OpEffectMonotonicity.cfg_comp cN))) = true.
Proof.
  exact OpEffectMonotonicity.op_effect_monotonicity_empty_start.
Qed.

Theorem par_confluence_concrete :
  forall (c c1 c2 : OpEffectMonotonicity.par_config),
    OpEffectMonotonicity.step_a c c1 ->
    OpEffectMonotonicity.step_b c c2 ->
    exists c',
      OpEffectMonotonicity.step_b c1 c' /\
      OpEffectMonotonicity.step_a c2 c' /\
      OpEffectMonotonicity.slot_a c' = S (OpEffectMonotonicity.slot_a c) /\
      OpEffectMonotonicity.slot_b c' = S (OpEffectMonotonicity.slot_b c).
Proof.
  exact OpEffectMonotonicity.par_confluence_diamond.
Qed.

(** ** Additional concrete citations (2026-04-20) *)

(** Multi-step preservation (corollary of subject reduction).
    Forwarding citation for downstream reference. *)
Theorem multi_preservation_concrete :
  forall (G : OpProgressSubject.context)
         (e : OpProgressSubject.expr)
         (T : OpProgressSubject.ty)
         (e' : OpProgressSubject.expr),
    OpProgressSubject.has_type G e T ->
    OpProgressSubject.multi_step e e' ->
    OpProgressSubject.has_type G e' T.
Proof.
  exact OpProgressSubject.op_multi_preservation.
Qed.

(** Type soundness: well-typed closed terms don't get stuck. *)
Theorem type_soundness_concrete :
  forall (e : OpProgressSubject.expr)
         (T : OpProgressSubject.ty)
         (e' : OpProgressSubject.expr),
    OpProgressSubject.has_type [] e T ->
    OpProgressSubject.multi_step e e' ->
    OpProgressSubject.value e' \/
    exists e'', OpProgressSubject.step e' e''.
Proof.
  exact OpProgressSubject.op_type_soundness.
Qed.

(** Gas strict decrease on steps.  Citation for op.tex §2.3. *)
Theorem gas_decreases_concrete :
  forall c c',
    OpConcreteAST.step c c' ->
    OpConcreteAST.gas c' < OpConcreteAST.gas c.
Proof.
  exact OpConcreteAST.gas_decreases.
Qed.
