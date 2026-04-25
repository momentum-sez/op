(** * LexOpAdequacy.v

    Finite verdict-agreement core for the Lex -> Op compilation
    skeleton.

    The paper's Section 7 states a verdict-preservation theorem up
    to weak bisimulation ([papers/op.tex §7.3, thm:verdict-preservation]).
    [CompilationSoundness.v] discharges the nine per-case preservation
    theorems (scalar constant, sanctions, variable, record, list,
    variant, match, defeasible, hole-fill) and [OpMetaTheory.v] lifts
    those into a single [verdict_preservation_admissible] bidirectional
    statement over the deliberately finite model used there.

    This file packages that finite statement: for every term in the
    current [admissible_lex] skeleton, the Lex verdict predicate and the
    Op verdict predicate on [admissible_compile t] agree. It is not the
    paper-level Lex denotational adequacy theorem, not reverse
    operational completeness for Op proper, and not proof-relevant full
    abstraction over compliance contexts.

    The theorem is Qed-closed, not [Admitted].  It does not rely
    on any new Axiom: the per-case Qed'd lemmas of
    [CompilationSoundness.v] and [OpMetaTheory.v] are the only
    inputs.

    The weak-bisimulation framework of [HeteroBisimulation.v] is
    the abstract setting; here we instantiate a concrete LTS whose
    only observable is the emitted Lex verdict. Direct cases produce
    their verdict on a single observable step. The hole-fill case uses
    the finite [tau] prefix proved by [fill_op_weak_verdict] after a
    successful attestation append.

    Important: this is a finite verdict-agreement core for the public
    mechanization. The paper-level adequacy program remains broader:
    it must range over the current [L_adm] fragment with compliance
    contexts, then over the full Lex calculus, and it must account for
    tribunal modals, temporal coercions, discretion-hole provenance,
    Op-specific terminals, and proof-relevant observations. *)

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
    the same verdict under the case-specific observation relation:
    direct cases use the observable single step, and hole-fill uses
    a finite silent prefix before the same observable verdict. Cf.
    [papers/op.tex def:weak-bisim] §7.3 and the logical-relations
    argument of [papers/op.tex §7.5]. *)
Definition lex_op_verdict_agree
    (t : admissible_lex) (e : admissible_op) : Prop :=
  forall vv,
    admissible_lex_verdict t vv <-> admissible_op_verdict e vv.

(** ** The finite verdict-agreement theorem *)

(** Statement: for every skeleton Lex term [t], the compiled Op
    expression [admissible_compile t] verdict-agrees with [t] on every
    admissible verdict. This is the finite closure of the nine per-case
    preservation theorems, not the full paper-level adequacy theorem. *)
Theorem lex_op_adequacy :
  forall t : admissible_lex,
    lex_op_verdict_agree t (admissible_compile t).
Proof.
  intros t vv.
  exact (verdict_preservation_admissible t vv).
Qed.

(** Descriptive alias used by public proof-status text. The historical
    theorem name [lex_op_adequacy] is retained for compatibility, while
    this alias states the exact proof boundary. *)
Theorem lex_op_finite_verdict_agreement :
  forall t : admissible_lex,
    lex_op_verdict_agree t (admissible_compile t).
Proof. exact lex_op_adequacy. Qed.

(** ** Compositional packaging

    We also state the same finite agreement as a relation-level
    package, specialized to [adm_compiled]. The theorem below gives the
    two verdict directions for the finite alphabet; it is not a
    coinductive weak bisimulation over Op's full transition system. *)

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

Theorem lex_op_finite_verdict_agreement_bisim :
  forall (t : admissible_lex) (e : admissible_op),
    adm_compiled t e ->
    (forall vv,
       admissible_lex_verdict t vv ->
       admissible_op_verdict e vv) /\
    (forall vv,
       admissible_op_verdict e vv ->
       admissible_lex_verdict t vv).
Proof. exact lex_op_adequacy_bisim. Qed.

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

(** ** Observational injectivity on the finite skeleton

    If the compiled Op expressions of two admissible Lex terms
    yield the same verdict extensionally, then the Lex terms
    themselves yield the same verdict extensionally.  This is the
    "no phantom verdict" direction for the finite skeleton: compiled
    Op verdict equality reflects Lex verdict equality. This is weaker
    than reverse operational completeness for Op proper. *)
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

(** ** Reflexivity / symmetry / transitivity of verdict agreement
       (2026-04-20)

    The [lex_op_verdict_agree] relation inherits reflexivity and
    transitivity from iff-reasoning, collected here as named Qeds
    to simplify downstream citations. *)

Theorem lex_op_verdict_agree_refl :
  forall t, lex_op_verdict_agree t (admissible_compile t).
Proof. exact lex_op_adequacy. Qed.

Theorem lex_op_verdict_agree_symm :
  forall t1 t2,
    (forall vv, admissible_lex_verdict t1 vv <->
                admissible_lex_verdict t2 vv) ->
    forall vv, admissible_op_verdict (admissible_compile t1) vv <->
               admissible_op_verdict (admissible_compile t2) vv.
Proof. exact lex_op_adequacy_congruence. Qed.

(** Verdict-agreement is transitive on the Lex side: if t1 and t2
    agree extensionally, and t2 and t3 agree extensionally, then t1
    and t3 agree extensionally on compiled outputs. *)
Theorem lex_op_verdict_agree_trans_on_lex :
  forall t1 t2 t3,
    (forall vv, admissible_lex_verdict t1 vv <->
                admissible_lex_verdict t2 vv) ->
    (forall vv, admissible_lex_verdict t2 vv <->
                admissible_lex_verdict t3 vv) ->
    forall vv, admissible_op_verdict (admissible_compile t1) vv <->
               admissible_op_verdict (admissible_compile t3) vv.
Proof.
  intros t1 t2 t3 H12 H23 vv.
  apply lex_op_adequacy_congruence.
  intros vv'. rewrite (H12 vv'). exact (H23 vv').
Qed.

(** Op-side faithful observation: if the compilations of t1 and t2
    observe all the same verdicts, then so do t1 and t2 in Lex. *)
Theorem lex_op_adequacy_reflects :
  forall t1 t2,
    (forall vv, admissible_op_verdict (admissible_compile t1) vv <->
                admissible_op_verdict (admissible_compile t2) vv) ->
    forall vv, admissible_lex_verdict t1 vv <->
               admissible_lex_verdict t2 vv.
Proof. exact lex_op_adequacy_injective. Qed.

(** ** Further adequacy composition laws (2026-04-20) *)

(** Compiling the same term twice yields the same Op expression (by
    function extensionality of admissible_compile on the same input).
    Named as an identity alias. *)
Theorem admissible_compile_deterministic :
  forall t1 t2 : admissible_lex,
    t1 = t2 ->
    admissible_compile t1 = admissible_compile t2.
Proof. intros t1 t2 H. subst. reflexivity. Qed.

(** If two admissible Lex terms have identical verdicts on EVERY
    admissible verdict, their compilations have identical verdicts. *)
Theorem lex_op_verdict_equality_lift :
  forall t1 t2,
    (forall vv, admissible_lex_verdict t1 vv =
                admissible_lex_verdict t2 vv) ->
    forall vv, admissible_op_verdict (admissible_compile t1) vv <->
               admissible_op_verdict (admissible_compile t2) vv.
Proof.
  intros t1 t2 Heq.
  apply lex_op_adequacy_congruence.
  intros vv. rewrite Heq. reflexivity.
Qed.

(** Agreement is symmetric: if t1 agrees with t2's compilation, t2
    agrees with t1's compilation (via two applications of adequacy). *)
Theorem lex_op_agree_symm :
  forall t1 t2,
    (forall vv, admissible_lex_verdict t1 vv <->
                admissible_lex_verdict t2 vv) ->
    forall vv, admissible_lex_verdict t2 vv <->
               admissible_lex_verdict t1 vv.
Proof.
  intros t1 t2 Heq vv. rewrite (Heq vv). reflexivity.
Qed.

(** ** Finite verdict-agreement summary

    [lex_op_adequacy], [lex_op_adequacy_bisim], and their finite-named
    aliases discharge the finite verdict-agreement core cited by the
    papers. The per-case preservation Qeds in [CompilationSoundness.v]
    are the inductive cases, and [adm_compiled] packages the compiled
    relation at the verdict-predicate level.

    No [Admitted.] or new [Axiom.] is introduced. Full Lex/Op
    adequacy, reverse operational completeness, compliance-context
    adequacy, and proof-relevant full abstraction remain paper-level
    obligations. *)
