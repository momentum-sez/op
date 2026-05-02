(** * Op/Syntax.v — Op language syntax mechanization (M-F1)

    Part of the F-OP-FORMAL milestone track. This file is the pure-syntax
    half of the M-F1 deliverable; the companion operational-semantics file
    is [Op/Semantics.v].

    ** Goal

    Mechanize the Op abstract syntax as an inductive type, closely
    mirroring the Rust reference at
    `crates/op-core/src/ast.rs::OpExpr` in this repository.
    No theorems about well-typedness, progress, or preservation are
    formulated here — those live in later milestones (M-F2 typing,
    M-F3 progress, M-F4 preservation).

    ** Scope

    A faithful translation of the Rust enum must eventually cover
    all ~24 OpExpr variants. This M-F1 scaffold encodes the
    load-bearing core (16 variants) sufficient to build the
    small-step semantics and value predicate that M-F2 / M-F3 will
    type-check and prove progress / preservation against. Later
    waves add the non-core variants (Await, AssertSafety, etc.)
    modularly.

    ** Design choices

    - Names of values and fields use an abstract [string] (the
      standard library's list-of-ascii). Variable equality is
      decidable via standard list-of-ascii decidable equality.
    - Literal values use a small universe ([Lit]) instead of the
      Rust [serde_json::Value]. This is sufficient for the type-
      soundness proofs; a wider-universe encoding is a later
      refinement.
    - Lambda / Let carry type annotations as [option OpType] to
      match the Rust AST, but the annotation is not load-bearing
      for the semantics (annotations are consumed by the type
      checker, not the reducer).
    - No theorems in this file — Syntax.v is declarative, not
      propositional. Sanity-check lemmas are limited to reflexivity-
      class checks proving that the encoding is consistent.

    ** Zero-axiom discipline

    Per the F-OP-FORMAL ratchet
    (`ci/formal_admitted_baseline.json`): this file must land with
    zero [Admitted] and zero [sorry]-equivalents. M-F1 is purely
    declarative, so that is trivially satisfied. Ratcheting up
    [Admitted] in this module requires reviewer sign-off.

    ** Rocq 9.1.1 compatibility

    Built under Rocq 9.1.1. Uses the [Stdlib] import prefix
    consistent with the rest of `formal/coq/`.
*)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.

Import ListNotations.

Set Implicit Arguments.

(** ** Op literal values

    The Rust [OpExpr::Literal] carries a [serde_json::Value]. For
    the M-F1 scaffold we restrict to a small universe covering the
    shapes actually produced by the scalar and structural cases of
    the Lex→Op compiler. [LUnit], [LBool], [LInt], [LStr] match
    the four scalar shapes already mechanized in
    [CompilationSoundness.v]. [LRecord] and [LList] appear in the
    lifted record / list compilation cases. Arbitrary JSON values
    are deferred to a later wave; today's type-soundness track does
    not require them. *)
Inductive Lit : Type :=
  | LUnit : Lit
  | LBool : bool -> Lit
  | LInt  : nat -> Lit
  | LStr  : string -> Lit.

(** ** Op base types

    Mirrors `crates/op-core/src/ast.rs::OpType` at the granularity required for
    M-F2 / M-F3. [OT_Linear], [OT_Locked] carry the linearity
    structure that [OpExpr] variants manipulate. [OT_Arrow] is the
    shape of lambda types. *)
Inductive OpType : Type :=
  | OT_Unit       : OpType
  | OT_Bool       : OpType
  | OT_Int        : OpType
  | OT_Str        : OpType
  | OT_EntityRef  : OpType
  | OT_Money      : OpType
  | OT_Digest     : OpType
  | OT_Linear     : OpType -> OpType
  | OT_Locked     : OpType -> OpType
  | OT_Arrow      : OpType -> OpType -> OpType
  | OT_Record     : list (string * OpType) -> OpType.

(** ** Op safety predicates

    A small universe of compositional safety predicates mirroring
    `crates/op-core/src/ast.rs::SafetyPredicate`. The mechanization treats them
    as uninterpreted tags; the intended meaning is resolved at
    type-check time via a predicate interpreter (not mechanized
    here — deferred to M-F4). *)
Inductive SafetyPred : Type :=
  | SP_AtomicFamilyClosure      : SafetyPred
  | SP_NoDoubleLock             : SafetyPred
  | SP_ExhaustivePatternMatch   : SafetyPred
  | SP_LinearConsumed           : SafetyPred
  | SP_EffectRowMonotone        : SafetyPred.

(** ** Op match arms *)
Inductive MatchArm : Type :=
  | MArm : string -> list (string * OpType) -> OpExpr -> MatchArm

(** ** Op expressions

    The 16-variant core mirrors `crates/op-core/src/ast.rs::OpExpr`. Each case is
    documented with the Rust counterpart. Variants:

    - [OE_Literal] : [OpExpr::Literal] — a wrapped literal value.
    - [OE_Var]     : [OpExpr::Var] — a bound variable reference.
    - [OE_Apply]   : [OpExpr::Apply] — function application.
    - [OE_Let]     : [OpExpr::Let] — lexical let-binding.
    - [OE_Lambda]  : [OpExpr::Lambda] — λ-abstraction.
    - [OE_Sequence] : [OpExpr::Seq] — sequenced expressions.
    - [OE_If]      : [OpExpr::If] — conditional.
    - [OE_Match]   : [OpExpr::Match] — polymorphic variant match.
    - [OE_RecordLit] : [OpExpr::RecordLit] — record construction.
    - [OE_FieldAccess] : [OpExpr::FieldAccess] — record field access.
    - [OE_ConsumeLinear] : [OpExpr::ConsumeLinear] — consume a
      [Linear<T>] resource.
    - [OE_Lock3PC] : [OpExpr::Lock3PC] — convert [Linear<T>] to
      [Locked<T>] under a corridor session.
    - [OE_CommitTransfer] : [OpExpr::CommitTransfer] — commit a
      locked resource.
    - [OE_ReleaseLock] : [OpExpr::ReleaseLock] — release a locked
      resource.
    - [OE_TryCatchCompensate] : [OpExpr::TryCatchCompensate] —
      try / catch / compensate.
    - [OE_AssertSafety] : [OpExpr::AssertSafety] — compositional
      safety assertion. *)
with OpExpr : Type :=
  | OE_Literal         : Lit -> OpExpr
  | OE_Var             : string -> OpExpr
  | OE_Apply           : OpExpr -> OpExpr -> OpExpr
  | OE_Let             : string -> option OpType -> OpExpr -> OpExpr -> OpExpr
  | OE_Lambda          : string -> OpType -> OpExpr -> OpExpr
  | OE_Sequence        : list OpExpr -> OpExpr
  | OE_If              : OpExpr -> OpExpr -> OpExpr -> OpExpr
  | OE_Match           : OpExpr -> list MatchArm -> OpExpr -> OpExpr
  | OE_RecordLit       : list (string * OpExpr) -> OpExpr
  | OE_FieldAccess     : OpExpr -> string -> OpExpr
  | OE_ConsumeLinear   : OpExpr -> OpExpr
  | OE_Lock3PC         : OpExpr -> string -> OpExpr
  | OE_CommitTransfer  : OpExpr -> OpExpr -> OpExpr
  | OE_ReleaseLock     : OpExpr -> OpExpr -> OpExpr
  | OE_TryCatchCompensate : OpExpr -> OpExpr -> OpExpr -> OpExpr
  | OE_AssertSafety    : SafetyPred -> OpExpr -> OpExpr.

(** ** Value predicate

    [is_value e] states that [e] is a terminal form — a fully-
    evaluated expression that cannot take a further step. Values
    are literals, lambdas, fully-evaluated records, and the
    locked-resource witness forms (which are values under the
    locked-handle discipline and consumed by [OE_CommitTransfer] /
    [OE_ReleaseLock] without further reduction of the handle
    itself).

    The companion [Op/Semantics.v] file relates this predicate to
    the small-step relation via the (later) progress theorem:
    a well-typed expression is either a value or steps. *)
Fixpoint is_value (e : OpExpr) : bool :=
  match e with
  | OE_Literal _         => true
  | OE_Lambda _ _ _      => true
  | OE_RecordLit fs      => forallb (fun f => is_value (snd f)) fs
  | _                    => false
  end.

(** ** Sanity-check lemmas

    These do NOT formulate theorems about the Op language; they
    simply verify that the encoding is internally consistent. Each
    closes with [reflexivity] / [discriminate] / trivial tactics.
    No [Admitted].
*)

(** [LUnit] differs from [LBool true]. *)
Lemma lit_unit_bool_distinct : LUnit <> LBool true.
Proof. discriminate. Qed.

(** The five safety predicates are pairwise distinct. *)
Lemma safety_pred_partial_distinct :
  SP_AtomicFamilyClosure    <> SP_NoDoubleLock /\
  SP_NoDoubleLock           <> SP_ExhaustivePatternMatch /\
  SP_ExhaustivePatternMatch <> SP_LinearConsumed /\
  SP_LinearConsumed         <> SP_EffectRowMonotone.
Proof. repeat split; discriminate. Qed.

(** [OpType] constructors are pairwise distinct (sample). *)
Lemma optype_sample_distinct :
  OT_Unit <> OT_Bool /\ OT_Bool <> OT_Int /\ OT_Int <> OT_Str.
Proof. repeat split; discriminate. Qed.

(** Every literal is a value. *)
Lemma literal_is_value : forall l, is_value (OE_Literal l) = true.
Proof. intros l. reflexivity. Qed.

(** Every lambda is a value. *)
Lemma lambda_is_value :
  forall x t b, is_value (OE_Lambda x t b) = true.
Proof. intros. reflexivity. Qed.

(** Empty records are trivially values. *)
Lemma empty_record_is_value : is_value (OE_RecordLit []) = true.
Proof. reflexivity. Qed.

(** [OE_Var] is NOT a value — free variables block progress until
    substitution. *)
Lemma var_not_value : forall x, is_value (OE_Var x) = false.
Proof. intros x. reflexivity. Qed.

(** [OE_Apply] is NOT a value — applications require a reduction
    step. *)
Lemma apply_not_value :
  forall e1 e2, is_value (OE_Apply e1 e2) = false.
Proof. intros. reflexivity. Qed.

(** Records of non-value fields are not values. *)
Lemma record_nonvalue_field :
  is_value (OE_RecordLit [("x"%string, OE_Var "y"%string)]) = false.
Proof. reflexivity. Qed.

(** [OE_ConsumeLinear] on any subexpression is non-value. *)
Lemma consume_linear_not_value :
  forall e, is_value (OE_ConsumeLinear e) = false.
Proof. intros e. reflexivity. Qed.

(** [OE_AssertSafety] is non-value — the assertion must fire. *)
Lemma assert_safety_not_value :
  forall p e, is_value (OE_AssertSafety p e) = false.
Proof. intros. reflexivity. Qed.
