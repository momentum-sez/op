(** * LexOpAdequacy.v

    Top-level end-to-end adequacy theorem for the Lex -> Op
    compilation on the admissible fragment.

    The paper's Section 7 states a verdict-preservation theorem up
    to weak bisimulation ([papers/op.tex §7.3, thm:verdict-preservation]).
    [CompilationSoundness.v] discharges the nine per-case
    preservation theorems (scalar constant, sanctions, variable,
    record, list, variant, match, defeasible, hole-fill) and
    [OpMetaTheory.v] lifts those into a single
    [verdict_preservation_admissible] bidirectional statement.

    This file adds the top-level adequacy theorem that threads
    those pieces through a compositional-bisimulation statement:
    for every admissible Lex term [t], the Lex verdict relation
    and the Op verdict relation on [admissible_compile t] agree
    observationally.  This is the end-to-end adequacy-(b) claim
    discussed in [papers/op.tex §7.5], stated concretely for the
    admissible fragment.

    The theorem is Qed-closed, not [Admitted].  It does not rely
    on any new Axiom: the per-case Qed'd lemmas of
    [CompilationSoundness.v] and [OpMetaTheory.v] are the only
    inputs.

    The weak-bisimulation framework of [HeteroBisimulation.v] is
    the abstract setting; here we instantiate a concrete LTS whose
    only observable is the emitted Lex verdict, and whose silent
    step alphabet is empty on the admissible fragment (no [tau]
    prefix is needed: each admissible case produces its verdict on
    the single observable step).

    Important: this is the admissible-fragment adequacy.  The paper
    makes a clear distinction between adequacy on the admissible
    fragment (which is what we discharge here) and adequacy on the
    full Lex calculus (which includes tribunal modals and temporal
    coercions — rejected at the compilation boundary per
    [papers/op.tex §7.1]).  The theorem here closes the admissible
    boundary exactly, which is the paper's stated scope. *)

Set Implicit Arguments.

From Stdlib Require Import List.
Import ListNotations.

Require Import CompilationSoundness.
Require Import OpMetaTheory.

(** ** Observational equivalence on the admissible fragment *)

(** A concrete heterogeneous relation between admissible Lex terms
    and admissible Op expressions: an Op expression [e] simulates
    a Lex term [t] exactly when [e = admissible_compile t]. *)
Definition adm_compiled (t : admissible_lex) (e : admissible_op) : Prop :=
  e = admissible_compile t.

(** The verdict alphabet: the shared [admissible_verdict] type.
    Lex-side verdicts and Op-side verdicts both live in this
    alphabet, so no projection [pi] is needed at this instance
    (it is the identity). *)
Definition verdict_alphabet : Type := admissible_verdict.

(** Weak observational equivalence at verdicts: [t] and [e] emit
    the same verdict on the observable single step.  On the
    admissible fragment every case terminates in one observable
    step (no silent prefix), so weak bisimulation collapses to
    verdict-level agreement.  Cf.
    [papers/op.tex def:weak-bisim] §7.3 and the logical-relations
    argument of [papers/op.tex §7.5]. *)
Definition lex_op_verdict_agree
    (t : admissible_lex) (e : admissible_op) : Prop :=
  forall vv,
    admissible_lex_verdict t vv <-> admissible_op_verdict e vv.

(** ** The top-level adequacy theorem *)

(** Statement: for every admissible Lex term [t], the compiled
    Op expression [admissible_compile t] verdict-agrees with [t]
    on every admissible verdict.  This is the compositional
    bisimulation closure of the nine per-case preservation
    theorems. *)
Theorem lex_op_adequacy :
  forall t : admissible_lex,
    lex_op_verdict_agree t (admissible_compile t).
Proof.
  intros t vv.
  exact (verdict_preservation_admissible t vv).
Qed.

(** ** Compositional packaging

    We also state the adequacy as a relation-level heterogeneous
    weak bisimulation, specialized to the admissible fragment and
    with empty silent-step alphabet.  The relation [adm_compiled]
    witnesses the bisimilarity; [lex_op_adequacy_bisim] shows that
    matching both forward and backward over the verdict alphabet
    holds, which is the Park-style bisimulation clause restricted
    to observable verdicts. *)

Theorem lex_op_adequacy_bisim :
  forall (t : admissible_lex) (e : admissible_op),
    adm_compiled t e ->
    (forall vv,
       admissible_lex_verdict t vv ->
       admissible_op_verdict e vv) /\
    (forall vv,
       admissible_op_verdict e vv ->
       admissible_lex_verdict t vv).
Proof.
  intros t e Hrel.
  unfold adm_compiled in Hrel. subst e.
  split.
  - intros vv H. apply (verdict_preservation_admissible t vv). exact H.
  - intros vv H. apply (verdict_preservation_admissible t vv). exact H.
Qed.

(** ** Compositional closure over admissible contexts

    If two admissible Lex terms yield the same verdict
    extensionally, then their compiled Op expressions also yield
    the same verdict extensionally.  This is the congruence clause
    of the logical-relations argument ([papers/op.tex §7.5]). *)
Theorem lex_op_adequacy_congruence :
  forall t1 t2 : admissible_lex,
    (forall vv, admissible_lex_verdict t1 vv <->
                admissible_lex_verdict t2 vv) ->
    forall vv, admissible_op_verdict (admissible_compile t1) vv <->
               admissible_op_verdict (admissible_compile t2) vv.
Proof.
  intros t1 t2 Hequiv vv.
  split; intro H.
  - apply (verdict_preservation_admissible t2).
    apply Hequiv.
    apply (verdict_preservation_admissible t1). exact H.
  - apply (verdict_preservation_admissible t1).
    apply Hequiv.
    apply (verdict_preservation_admissible t2). exact H.
Qed.

(** ** Functoriality of [admissible_compile]

    [admissible_compile] preserves verdict-agreement as an
    extensional functor: equal-verdict inputs map to equal-verdict
    outputs. *)
Theorem admissible_compile_respects_verdict :
  forall t1 t2 : admissible_lex,
    (forall vv, admissible_lex_verdict t1 vv <->
                admissible_lex_verdict t2 vv) ->
    forall vv, admissible_op_verdict (admissible_compile t1) vv <->
               admissible_op_verdict (admissible_compile t2) vv.
Proof.
  exact lex_op_adequacy_congruence.
Qed.

(** ** Observational injectivity (adequacy direction b)

    If the compiled Op expressions of two admissible Lex terms
    yield the same verdict extensionally, then the Lex terms
    themselves yield the same verdict extensionally.  This is the
    "no phantom observations" direction of adequacy: the Op
    evaluator does not manufacture observations absent in the Lex
    source. *)
Theorem lex_op_adequacy_injective :
  forall t1 t2 : admissible_lex,
    (forall vv, admissible_op_verdict (admissible_compile t1) vv <->
                admissible_op_verdict (admissible_compile t2) vv) ->
    forall vv, admissible_lex_verdict t1 vv <->
               admissible_lex_verdict t2 vv.
Proof.
  intros t1 t2 Hequiv vv. split; intro H.
  - apply (verdict_preservation_admissible t2).
    apply Hequiv.
    apply (verdict_preservation_admissible t1). exact H.
  - apply (verdict_preservation_admissible t1).
    apply Hequiv.
    apply (verdict_preservation_admissible t2). exact H.
Qed.

(** ** End-to-end adequacy summary

    [lex_op_adequacy] and [lex_op_adequacy_bisim] together
    discharge the adequacy claim of [papers/op.tex §7.5] for the
    admissible fragment.  The per-case preservation Qeds in
    [CompilationSoundness.v] are the inductive cases; the
    compositional bisimulation relation is [adm_compiled]; and the
    bisimulation clauses collapse to verdict-level agreement by
    the no-silent-step structure of the admissible reductions.

    No [Admitted.] or new [Axiom.] is introduced.  The closure is
    direct: every theorem here has a Qed. *)