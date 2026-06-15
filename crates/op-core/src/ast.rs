//! Op abstract syntax tree.
//!
//! An `OpProgram` denotes one executable operation family. The canonical
//! identity of a program is the pair `(operation_type, jurisdiction)`. The
//! language does not invent a second naming system.
//!
//! The semantic core has four objects: **steps**, **primitives**,
//! **compensation**, and **composition**. Steps are the smallest named unit
//! that consume input, produce output, declare effects, may suspend on a
//! callback, declare a failure policy, and expose an inverse branch. Primitives
//! are host-recognized actions with stable lowering rules. Compensation is a
//! typed inverse program over committed side effects; it is local to the step
//! it inverts. Composition is how steps form a workflow — sequential, parallel,
//! guarded choice, suspension/resumption, and scoped compensation.

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Programs
// ---------------------------------------------------------------------------

/// A complete Op program — the unit of compilation and type-checking.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpProgram {
    /// Qualified program name (e.g. `entity.incorporate`).
    pub name: String,
    /// Ambient jurisdiction. Becomes the primary `OperationDefinition.jurisdiction`
    /// when lowered. Use `"_default"` for the jurisdictionally generic base.
    pub jurisdiction: String,
    /// Program-level metadata.
    pub metadata: ProgramMetadata,
    /// Program input parameters, modeled as a record type.
    pub inputs: Vec<(String, OpType)>,
    /// Program output fields, modeled as a record type.
    pub outputs: Vec<(String, OpType)>,
    /// Program-level effect declaration (union of effects across all steps).
    pub effects: Vec<Effect>,
    /// Participants for multi-entity operations.
    pub participants: Vec<Participant>,
    /// Approval mode across participants.
    pub approval: Option<ApprovalMode>,
    /// Preconditions and postconditions at the program level.
    pub contracts: Contracts,
    /// The statement body of the program.
    pub body: Vec<Statement>,
    /// Gas budget declaration.
    pub gas_budget: GasBudget,
}

/// Program-level metadata.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct ProgramMetadata {
    /// Semantic version of the program.
    pub version: String,
    /// Free-form description.
    pub description: String,
}

/// Contracts attached to a program or step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct Contracts {
    /// Preconditions — what must hold before execution.
    pub requires: Vec<Contract>,
    /// Postconditions — what must hold after successful execution.
    pub ensures: Vec<Contract>,
}

/// A contract clause.
///
/// Per `docs/proposal-lex-rule-contract-and-pack-binding.md` §2.1, `LexRule`
/// references a Lex rule and carries the structural-discharge obligation the
/// program must satisfy. The type checker verifies, at compile time, that the
/// program body contains a structural witness for every `LexRule` in
/// `requires` (§3.2); an under-discharged program is rejected fail-closed. The
/// Lex evaluator is NEVER re-run at the Op boundary.
///
/// SCOPE (honest partial — see proposal §3 and the FOLLOW-ON in `types.rs`):
/// the §3.1 *completeness against the active pack* check (query the pack for
/// every rule whose `applies_to` matches `(operation_type, jurisdiction)` and
/// reject if `requires` omits one) is NOT implemented here. It needs a pack
/// handle on `CompileCtx` and the `lex-pack` crate (`Pack`,
/// `CompiledLexPredicate`, `Pack::rules_for`), neither of which exists yet
/// (companion `~/lex/docs/frontier-work/09` §3 — design-only). What IS
/// implemented and load-bearing is §3.2 per-rule structural discharge: the
/// obligation is carried explicitly on the ref (the canonical fully-explicit
/// form per proposal §4.1; `auto_lex`/pack population is sugar over it), so the
/// checker is decidable inside op-core with no external pack and rejects an
/// undischarged obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Contract {
    /// Shorthand: a set of compliance domains must be evaluated / satisfied.
    Domains(Vec<String>),
    /// A boolean expression (reduced against the post-typecheck environment).
    Expr(OpExpr),
    /// References a Lex rule supplied by the active pack. The type checker
    /// resolves the reference at program-compile time and verifies the
    /// program's steps structurally discharge the obligation it carries
    /// (`LexRuleRef.discharge`). The Lex evaluator is NEVER re-executed at the
    /// Op boundary.
    LexRule(LexRuleRef),
}

/// A typed reference to a Lex rule a program declares it discharges
/// (proposal §2.1).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexRuleRef {
    /// Content hash of the rule, as carried in the pack. BLAKE3 content
    /// addressing (`b3:<hex>`), matching the canonical Lex `Blake3Hash` form
    /// (`lex-core/src/ast.rs::Blake3Hash`) and proposal §2.2's
    /// `rule_hash:b3:0x...` surface.
    pub rule_hash: LexRuleHash,
    /// Declared jurisdiction. MUST match the program's `OpProgram.jurisdiction`
    /// exactly, OR be a wildcard explicitly covered by the rule's `applies_to`
    /// declaration (companion §2.1). Carried as a `QualIdent`.
    pub jurisdiction: QualIdent,
    /// Pinned pack version. The deterministic-replay binding (proposal §2.1 /
    /// §6): a validation/execution host re-checks the program against the same
    /// pack version. Op specifies only the reference shape; pack discovery,
    /// signature verification, and pinning are host concerns.
    pub pack_version: PackVersion,
    /// The structural-discharge obligation this rule places on the program
    /// body (proposal §3.2). When the `lex-pack` crate exists, the build-time
    /// host derives this from the rule's `CompiledLexPredicate.body`
    /// (`CompiledTerm`); until then it is carried explicitly on the ref (the
    /// canonical fully-explicit form, proposal §4.1). The type checker rejects
    /// the program if the body carries no witness for it.
    pub discharge: DischargeRequirement,
}

/// The content hash of a Lex rule as carried in the pack (proposal §2.1).
///
/// Mirrors the canonical Lex `Blake3Hash` (a BLAKE3 digest) rather than
/// inventing a second hash vocabulary: equality of `LexRuleHash` IS rule
/// identity (companion §3.2 — "equality is by hash, not name"). The string is
/// the BLAKE3 hex digest (optionally `b3:`-prefixed per the proposal surface);
/// op-core treats it as an opaque content-address and never re-hashes it.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LexRuleHash(pub String);

/// A pinned pack version (proposal §2.1, companion §3.4 — `(curator_did,
/// semver, content_digest)`). Carried as an opaque label at the op-core layer;
/// the structural meaning lives in `lex-pack`. The host pins it; Op only
/// records it so replay is exact.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PackVersion(pub String);

/// A qualified identifier — a jurisdiction code (`sc`, `hn-prospera`) or
/// operation-kind qualifier. Op already names its programs by string
/// `(operation_type, jurisdiction)`; this is the matching newtype for the
/// jurisdiction qualifier on a `LexRuleRef` (proposal §2.1). A bare `*` is the
/// wildcard form (companion §2.1).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct QualIdent(pub String);

impl QualIdent {
    /// Whether this qualifier is the explicit wildcard `*` (companion §2.1 —
    /// "all" is the explicit wildcard, not absence).
    pub fn is_wildcard(&self) -> bool {
        self.0 == "*"
    }
}

/// The structural-discharge obligation a `LexRule` places on a program body
/// (proposal §3.2). Each variant names a *syntactic witness* the type checker
/// looks for; discharge is decided in time linear in the program — no SMT, no
/// fixpoint, no re-execution of the Lex evaluator. This is the op-core-local
/// realization of the §3.2 `CompiledTerm` predicate-shape grammar; the listed
/// patterns are the proposal's four, and the grammar is extended only by joint
/// PR (proposal §3.2, §10.3).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DischargeRequirement {
    /// `requires sanctions_check on subject S` — discharged when the program
    /// contains a step (or expression) carrying the `sanctions_check` effect.
    /// This is also the §3.3 I-1 sanctions-terminal pattern: defense in depth
    /// alongside Op's own effect-safety rule that every write-class effect is
    /// dominated by a sanctions check.
    SanctionsCheck,
    /// `requires governance_request on policy P` — discharged when the program
    /// contains a step carrying the `governance_request` effect.
    GovernanceRequest,
    /// `requires obligation O before write` — discharged when every reachable
    /// write-class effect (`sovereign_write`, `identity_mutation`,
    /// `fiscal_transfer`) is dominated in the program body by a step that
    /// emits a `proof_emit` effect (the obligation). A program with a
    /// write-class effect and no preceding `proof_emit` fails.
    ObligationBeforeWrite,
    /// `ensures certificate C` — discharged when the program emits a
    /// `proof_emit` effect on some step before termination.
    CertificateEmitted,
}

// ---------------------------------------------------------------------------
// Participants (multi-entity workflows)
// ---------------------------------------------------------------------------

/// A declared participant in a multi-entity operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Participant {
    /// Local binding name (e.g. `acquirer`, `target`).
    pub name: String,
    /// Role.
    pub role: ParticipantRole,
    /// Expression evaluating to the participant's entity identifier.
    pub entity: OpExpr,
    /// Governance requirements this participant carries.
    pub governance: Vec<GovernanceRequirement>,
}

/// Participant roles. Matches the kernel runtime's role vocabulary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub enum ParticipantRole {
    /// Acquirer in an M&A-class operation.
    Acquirer,
    /// Target of an M&A-class operation.
    Target,
    /// Counterparty in a bilateral operation.
    Partner,
    /// Origin zone in a cross-zone operation.
    SourceZone,
    /// Destination zone in a cross-zone operation.
    DestinationZone,
    /// Generic participant.
    Participant,
}

/// Per-participant governance requirements.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum GovernanceRequirement {
    /// Board resolution requirement.
    BoardResolution {
        /// Quorum identifier (e.g. `"board_majority"`).
        quorum: String,
        /// Required roles (e.g. `["director"]`).
        required_roles: Vec<String>,
    },
    /// Shareholder vote requirement.
    ShareholderVote {
        /// Threshold in basis points.
        threshold_bps: u32,
    },
    /// Regulatory approval requirement.
    RegulatoryApproval {
        /// Authority identifier.
        authority: String,
    },
}

/// Approval composition across participants.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ApprovalMode {
    /// All participants must approve.
    Unanimous,
    /// Majority of participants must approve.
    Majority,
    /// Specific participants must approve.
    Specific {
        /// Required participant bindings.
        required: Vec<String>,
    },
    /// Bilateral: both named parties must approve.
    Bilateral,
}

// ---------------------------------------------------------------------------
// Types — the Op type system
// ---------------------------------------------------------------------------

/// Op type expression.
///
/// Op's base types are grounded in workflow-level kernel types, not in any
/// specific compliance-algebra or tensor shape. `EntityRef`, `JurisdictionRef`,
/// `MoneyAmount`, `ContentDigest`, and `CallbackEvent` are opaque to Op and
/// interpreted by the host.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum OpType {
    /// Unit type (no value).
    Unit,
    /// Boolean.
    Bool,
    /// Integer.
    Int,
    /// UTF-8 string.
    String,
    /// Calendar date.
    Date,
    /// Timestamp (wall-clock, UTC).
    Timestamp,
    /// Duration.
    Duration,

    /// Entity reference. Opaque to Op; interpreted by the host.
    EntityRef,
    /// Jurisdiction reference. Opaque to Op; interpreted by the host.
    JurisdictionRef,
    /// Monetary amount (currency + amount-in-minor-units, semantics in host).
    MoneyAmount,
    /// Content digest (host-opaque hash).
    ContentDigest,
    /// Callback event token.
    CallbackEvent,

    /// Linear (single-use) resource type.
    Linear(Box<OpType>),

    /// Affine-with-ghost-witness lock for three-phase commit.
    /// Has exactly two eliminators: commit-transfer, release-lock.
    Locked(Box<OpType>),

    /// Record type with named fields (structural).
    Record(Vec<(String, OpType)>),

    /// Variant (tagged union).
    Variant(Vec<(String, OpType)>),

    /// List.
    List(Box<OpType>),

    /// Optional.
    Option(Box<OpType>),

    /// Result.
    Result(Box<OpType>, Box<OpType>),

    /// Tuple.
    Tuple(Vec<OpType>),

    /// Awaited value: suspending step returns `Await<Event, Payload>`.
    Await {
        /// Callback event identifier (e.g. `"consent.approved"`).
        event: String,
        /// Payload type produced when the event fires.
        payload: Box<OpType>,
    },

    /// Non-dependent function type.
    Arrow(Box<OpType>, Box<OpType>),

    /// Named alias (resolved against the program's type environment).
    Named(String),
}

// ---------------------------------------------------------------------------
// Step signatures
// ---------------------------------------------------------------------------

/// A step signature `In -> Out ! Effects`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StepSignature {
    /// Input type.
    pub input: OpType,
    /// Output type.
    pub output: OpType,
    /// Effect row.
    pub effects: Vec<Effect>,
}

/// Alias retained for ergonomic imports.
pub type StepSig = StepSignature;

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

/// A statement in a program body.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Statement {
    /// Typed let binding: `let name: T = value;`.
    Let {
        /// Bound variable name.
        name: String,
        /// Annotated type.
        ty: OpType,
        /// Bound expression.
        value: OpExpr,
    },

    /// Step declaration: `step name : In -> Out ! E { body } compensate { ... }`.
    Step(OpStep),

    /// Short form: `run name = primitive_call(...);`.
    Run {
        /// Bound name for the step result.
        name: String,
        /// Primitive invocation.
        call: OpExpr,
    },

    /// Parallel block: `par { a = e1; b = e2; }`. Sibling branches share the
    /// incoming environment; sibling data-dependence is forbidden by the
    /// type system.
    Par {
        /// Parallel branches (each a `Let`-like binding).
        branches: Vec<(String, OpExpr)>,
    },

    /// Guarded choice: `choose { when cond -> { .. } else -> { .. } }`.
    Choose {
        /// Arms: each with a boolean guard and a statement block.
        arms: Vec<(OpExpr, Vec<Statement>)>,
        /// Else-block. Required when arms do not cover all cases observably.
        else_block: Option<Vec<Statement>>,
    },

    /// Jurisdiction scope: `in <jurisdiction> { ... }`.
    In {
        /// Jurisdiction identifier (string literal or variable).
        jurisdiction: String,
        /// Block.
        body: Vec<Statement>,
    },

    /// Policy block invoking a SAVM-like proof backend.
    /// The host decides how to lower the policy. Op preserves the scope.
    Policy {
        /// Policy name.
        name: String,
        /// Domains the policy proves.
        domains: Vec<String>,
    },

    /// `return <expr>` statement.
    Return(OpExpr),

    /// Naked expression statement (for effectful expressions whose value is
    /// discarded).
    Expr(OpExpr),
}

/// A single step — analogous to `StepDefinition` in the kernel runtime.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpStep {
    /// Step identifier (unique within the program).
    pub id: String,
    /// Primitive invocation or an inline block.
    pub body: StepBody,
    /// Typed step signature.
    pub signature: StepSignature,
    /// Optional wait semantics for suspending steps.
    pub wait: Option<WaitSpec>,
    /// Failure policy. `None` defaults to `CancelOperation`.
    pub on_failure: Option<FailureAction>,
    /// Local compensation clause.
    pub compensate: Option<CompensationClause>,
    /// Optional per-step contracts.
    pub contracts: Contracts,
}

/// A step body: either a primitive call or an inline block of statements.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum StepBody {
    /// Direct primitive call.
    Primitive(Primitive, Vec<(String, OpExpr)>),
    /// Inline block.
    Block(Vec<Statement>),
}

/// Wait specification for callback-suspended steps.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WaitSpec {
    /// Event identifier (e.g. `"consent.approved"`).
    pub event: String,
    /// Timeout in seconds.
    pub timeout_secs: u64,
}

/// Failure policy. Matches the kernel runtime's `OnFailure` vocabulary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FailureAction {
    /// Abort the operation and run full compensation.
    CancelOperation,
    /// Step-local rollback, continue execution.
    Rollback,
    /// Skip the step, continue with dependents as if it had completed with
    /// the unit value.
    Skip,
    /// Retry with exponential backoff.
    Retry {
        /// Maximum retry attempts.
        max_attempts: u32,
    },
    /// Continue silently.
    Continue,
}

/// Local compensation clause attached to a step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompensationClause {
    /// Inverse body.
    pub body: StepBody,
    /// Compliance domains whose attestation is invalidated by the rollback.
    pub invalidated_domains: Vec<String>,
}

/// A primitive identifier — dotted path (e.g. `create.entity`,
/// `consent.board_resolution`, `trade.lc_issue`).
///
/// Primitives are host-recognized actions. The language-layer gives them no
/// built-in meaning; the host supplies interpretations through `OpHost`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Primitive(pub String);

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

/// Op expression.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum OpExpr {
    /// Unit literal.
    Unit,
    /// Boolean literal.
    Bool(bool),
    /// Integer literal.
    Int(i64),
    /// String literal. Supports `${name}` interpolation resolved after typing.
    String(String),
    /// Null / option-none.
    Null,

    /// Variable reference.
    Var(String),

    /// Field access (`record.field`).
    Field(Box<OpExpr>, String),

    /// Record construction.
    Record(Vec<(String, OpExpr)>),

    /// List construction.
    List(Vec<OpExpr>),

    /// Tuple construction.
    Tuple(Vec<OpExpr>),

    /// Function / primitive call.
    Call(String, Vec<(String, OpExpr)>),

    /// Binary operator.
    BinOp(BinOp, Box<OpExpr>, Box<OpExpr>),

    /// Unary operator.
    UnOp(UnOp, Box<OpExpr>),

    /// `coalesce(a, b)` — returns `a` if non-null, else `b`.
    Coalesce(Box<OpExpr>, Box<OpExpr>),

    /// Sequential composition `Seq(a, b)` — evaluate `a` for its effect
    /// (value discarded), then evaluate `b` and return its value.
    ///
    /// Type: `type_of(Seq(a, b)) = type_of(b)`. Effect row:
    /// `effects(Seq(a, b)) = effects(a) ∪ effects(b)`.
    ///
    /// The compilation function for Lex filled-hole lowering emits
    /// `Seq(attestation_append_call, value)` so the attestation effect
    /// materializes into `mu` while the value preserves its Op-type.
    Seq(Box<OpExpr>, Box<OpExpr>),

    /// `await event within duration` — typed callback suspension.
    Await {
        /// Event identifier.
        event: String,
        /// Timeout in seconds.
        timeout_secs: u64,
    },

    /// Pattern match.
    Match {
        /// Scrutinee.
        scrutinee: Box<OpExpr>,
        /// Arms.
        arms: Vec<MatchArm>,
        /// Mandatory catch-all.
        catch_all: Box<OpExpr>,
    },

    /// Assert a compositional safety predicate.
    AssertSafety(SafetyPredicate),

    /// Consume a linear resource.
    ConsumeLinear(Box<OpExpr>),

    /// Convert `Linear<T>` to `Locked<T>` for three-phase commit.
    Lock {
        /// Resource to lock.
        resource: Box<OpExpr>,
        /// Corridor identifier.
        corridor_id: String,
    },

    /// Consume `Locked<T>` by committing the transfer.
    CommitTransfer {
        /// Locked handle.
        locked: Box<OpExpr>,
        /// Witness that the foreign zone minted the corresponding resource.
        witness: Box<OpExpr>,
    },

    /// Restore `Locked<T>` to `Linear<T>` by releasing the lock.
    ReleaseLock {
        /// Locked handle.
        locked: Box<OpExpr>,
        /// Witness that the foreign zone aborted.
        witness: Box<OpExpr>,
    },
}

/// Binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinOp {
    /// Equality.
    Eq,
    /// Inequality.
    Ne,
    /// Less-than.
    Lt,
    /// Less-than-or-equal.
    Le,
    /// Greater-than.
    Gt,
    /// Greater-than-or-equal.
    Ge,
    /// Logical and.
    And,
    /// Logical or.
    Or,
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Multiplication.
    Mul,
    /// Membership test (`in`).
    In,
    /// Substring / element containment.
    Contains,
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnOp {
    /// Logical negation.
    Not,
    /// Arithmetic negation.
    Neg,
}

/// Match arm.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatchArm {
    /// Constructor pattern name.
    pub pattern: String,
    /// Binder for the arm value.
    pub binding: String,
    /// Arm body.
    pub body: OpExpr,
}

/// An expression node bundled with an optional source span for diagnostics.
/// Retained as a convenience for compilers that want to preserve spans after
/// lowering; the language core does not require it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExprNode {
    /// The expression.
    pub expr: OpExpr,
    /// Optional source span (byte offsets).
    pub span: Option<(u32, u32)>,
}

// ---------------------------------------------------------------------------
// Effects
// ---------------------------------------------------------------------------

/// Tracked kernel effect.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, Hash)]
#[serde(rename_all = "snake_case")]
pub enum Effect {
    /// Pure computation.
    Pure,
    /// Read state.
    Read,
    /// Mutates sovereign-owned state.
    SovereignWrite,
    /// Mutates identity state.
    IdentityMutation,
    /// Moves or commits value.
    FiscalTransfer,
    /// Sanctions gate (mandatory).
    SanctionsCheck,
    /// Initiates a governance ceremony.
    GovernanceRequest,
    /// Produces a document artifact.
    DocumentGeneration,
    /// Reads external state.
    ExternalRead,
    /// Emits a proof obligation / attestation record.
    ProofEmit,
    /// Fuel-bounded iteration.
    Fuel(u64),
    /// Callback wait. The event identifier is carried in the inner string.
    Await(String),
}

// ---------------------------------------------------------------------------
// Gas budget
// ---------------------------------------------------------------------------

/// Two-tier gas budget: structural + extensional.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct GasBudget {
    /// Static structural gas bound (covers workflow skeleton).
    pub structural_gas: u64,
    /// Per-element extensional gas price.
    pub per_element_gas: u64,
    /// Cardinality certificate (if known at compile time).
    pub cardinality_certificate: Option<CardinalityCertificate>,
}

/// Cardinality certificate `(query, n, asof, signature)` — a host-issued
/// attestation bounding the number of elements a query returns at a point in
/// time.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CardinalityCertificate {
    /// The query whose cardinality is bounded.
    pub query: String,
    /// Maximum element count.
    pub cardinality: u64,
    /// Timestamp of attestation.
    pub as_of: String,
    /// Signature (host-opaque).
    pub signature: String,
}

// ---------------------------------------------------------------------------
// Outcome — the terminal set of program evaluation (§4.13)
// ---------------------------------------------------------------------------

/// Program-level terminal outcome.
///
/// Per the Op paper §4.13 "Terminal set", every reduction from a typed
/// initial configuration under a finite gas budget reaches exactly one of
/// seven terminals. `Outcome` encodes that enumeration at the type level:
/// any pattern match on `Outcome` that forgets a variant is a compile-time
/// error. The enum is the machine-checkable witness that the terminal set
/// has cardinality seven.
///
/// 1. `Value` — reduction completed with a result value.
/// 2. `Paused` — evaluation suspended on a callback event; the resume token
///    is carried in the variant payload.
/// 3. `Halted` — host or runtime aborted the program on a named reason
///    (non-gas, non-sanctions termination).
/// 4. `SanctionsBlocked` — a dominating sanctions gate rejected the
///    program's principal; no further reduction.
/// 5. `OutOfStructuralGas` — the static structural budget was exhausted.
/// 6. `OutOfCompensationGas` — the compensation-reserve budget was
///    exhausted while executing an inverse path.
/// 7. `Timeout` — an `await` exceeded its declared `within` duration.
///
/// The variants are payload-carrying so the terminal is self-describing;
/// downstream callers read the payload for the specific diagnostic they
/// need without re-inspecting the program.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Outcome {
    /// Reduction completed with a result value (serialized as JSON for
    /// host portability).
    Value(serde_json::Value),
    /// Execution is paused on a callback event `(event, resume_token)`.
    Paused {
        /// Callback event identifier.
        event: String,
        /// Opaque resume token for the runtime to continue evaluation.
        resume_token: String,
    },
    /// Program halted with a named reason (non-gas, non-sanctions).
    Halted {
        /// Human-readable halt reason.
        reason: String,
    },
    /// A sanctions gate rejected the dominating principal.
    SanctionsBlocked {
        /// Principal identifier that was blocked.
        principal: String,
    },
    /// Structural gas exhaustion.
    OutOfStructuralGas {
        /// Structural gas consumed at the point of failure.
        used: u64,
        /// Configured structural-gas limit.
        limit: u64,
    },
    /// Compensation gas exhaustion.
    ///
    // FOLLOW-ON: this terminal variant is part of the §4.13 seven-terminal
    // enumeration, but no compensation-gas *reserve* logic in-tree produces it
    // yet. A reserve would require: a distinct compensation-gas budget carried
    // alongside `GasBudget`, a runtime reduction evaluator that debits it while
    // executing an inverse (compensation) path, and emission of this terminal
    // when the reserve is exhausted. The current `gas` module meters forward
    // structural/extensional gas only and ships no evaluator to thread it (see
    // the README gas-model note), so this variant is reachable by construction
    // of the enum but is not yet driven by execution. It is a feature, not a
    // soundness bug; left unimplemented in this pass.
    OutOfCompensationGas {
        /// Compensation gas consumed at the point of failure.
        used: u64,
        /// Configured compensation-gas reserve.
        limit: u64,
    },
    /// An `await` exceeded its declared duration.
    Timeout {
        /// Event identifier the program was awaiting.
        event: String,
        /// Timeout in seconds, as declared in the `await`.
        timeout_secs: u64,
    },
}

// ---------------------------------------------------------------------------
// Compositional safety predicates
// ---------------------------------------------------------------------------

/// Compositional safety predicates — compile-time type errors for aggregate
/// attack classes. Host-supplied predicates may extend this set via `Custom`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SafetyPredicate {
    /// Group formation bypass via multiple shell entities with shared
    /// beneficial owners.
    NoGroupFormationBypass,
    /// Beneficial-ownership concentration below disclosure threshold.
    NoBeneficialOwnershipConcentration {
        /// Disclosure threshold percentage.
        threshold_pct: u32,
    },
    /// Cross-border threshold fragmentation.
    NoCrossBorderThresholdFragmentation,
    /// Coordinated sanctions evasion across coordinated parties.
    NoCoordinatedSanctionsEvasion,
    /// Disclosure threshold fragmentation across shareholder classes.
    NoDisclosureFragmentation,
    /// Host-specific predicate carrying an identifier.
    Custom(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linear_type_construction() {
        let share_cert = OpType::Linear(Box::new(OpType::Record(vec![
            ("share_class".to_string(), OpType::String),
            ("quantity".to_string(), OpType::Int),
            ("entity_id".to_string(), OpType::EntityRef),
        ])));
        assert!(matches!(share_cert, OpType::Linear(_)));
    }

    #[test]
    fn locked_type_for_three_phase_commit() {
        let locked = OpType::Locked(Box::new(OpType::Linear(Box::new(OpType::String))));
        assert!(matches!(locked, OpType::Locked(_)));
    }

    #[test]
    fn await_type_shape() {
        let a = OpType::Await {
            event: "consent.approved".to_string(),
            payload: Box::new(OpType::Record(vec![(
                "consent_id".to_string(),
                OpType::String,
            )])),
        };
        assert!(matches!(a, OpType::Await { .. }));
    }

    #[test]
    fn safety_predicate_serde_roundtrip() {
        let pred = SafetyPredicate::NoBeneficialOwnershipConcentration { threshold_pct: 25 };
        let json = serde_json::to_string(&pred).unwrap();
        let back: SafetyPredicate = serde_json::from_str(&json).unwrap();
        assert_eq!(pred, back);
    }

    #[test]
    fn gas_budget_serde_roundtrip() {
        let budget = GasBudget {
            structural_gas: 1000,
            per_element_gas: 10,
            cardinality_certificate: Some(CardinalityCertificate {
                query: "shareholders(entity_id=X)".to_string(),
                cardinality: 4300,
                as_of: "2026-04-18T10:00:00Z".to_string(),
                signature: "host-sig:abc".to_string(),
            }),
        };
        let json = serde_json::to_string(&budget).unwrap();
        let back: GasBudget = serde_json::from_str(&json).unwrap();
        assert_eq!(budget, back);
    }

    #[test]
    fn step_signature_roundtrip() {
        let sig = StepSignature {
            input: OpType::Record(vec![("amount".to_string(), OpType::MoneyAmount)]),
            output: OpType::Record(vec![("invoice_id".to_string(), OpType::String)]),
            effects: vec![Effect::FiscalTransfer, Effect::SovereignWrite],
        };
        let json = serde_json::to_string(&sig).unwrap();
        let back: StepSignature = serde_json::from_str(&json).unwrap();
        assert_eq!(sig, back);
    }

    #[test]
    fn participant_role_vocabulary() {
        let roles = [
            ParticipantRole::Acquirer,
            ParticipantRole::Target,
            ParticipantRole::Partner,
            ParticipantRole::SourceZone,
            ParticipantRole::DestinationZone,
            ParticipantRole::Participant,
        ];
        for r in &roles {
            let json = serde_json::to_string(r).unwrap();
            let back: ParticipantRole = serde_json::from_str(&json).unwrap();
            assert_eq!(*r, back);
        }
    }
}
