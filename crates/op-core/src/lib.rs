//! # op-core — Op Workflow Language
//!
//! Op is a typed effectful workflow language for multi-step economic programs.
//! This crate ships the language core: AST, type system, effect system, gas
//! model, deterministic evaluator, and host-abstraction trait.
//!
//! ## Typing judgment
//!
//! `Gamma |- e : T ! E`
//!
//! where `Gamma` is the variable environment, `T` is the result type, and `E`
//! is the effect row. Effect rows compose by union; some effect pairs impose
//! ordering constraints.
//!
//! ## Type system
//!
//! - **Base types** — scalars grounded in workflow data: `String`, `Bool`,
//!   `Int`, `Date`, `Timestamp`, `Duration`, and the host-parameterized
//!   opaques `EntityRef`, `JurisdictionRef`, `MoneyAmount`, `ContentDigest`,
//!   `CallbackEvent`.
//! - **Structural types** — records, variants, lists, optionals, tuples.
//! - **Linear types** — `Linear<T>` for single-use resources.
//! - **Locked types** — `Locked<T>` with exactly two eliminators
//!   (commit-transfer, release-lock), suitable for three-phase commit.
//! - **Await types** — `Await<Event, Payload>` distinguishes suspended
//!   execution from completion at the type level.
//!
//! ## Effect system
//!
//! Tracked kernel effects:
//! - `sovereign_write` — mutates sovereign state
//! - `identity_mutation` — modifies identity state
//! - `fiscal_transfer` — moves or commits value
//! - `sanctions_check` — mandatory gate
//! - `governance_request` — initiates a governance ceremony
//! - `document_generation` — produces a document artifact
//! - `external_read` — reads external state
//! - `proof_emit` — emits proof obligations / attestations
//! - `await <event>` — suspends on a callback
//!
//! Safety rule: any reachable `sovereign_write`, `identity_mutation`, or
//! `fiscal_transfer` must be dominated by a `sanctions_check`, with one
//! deferred-subject exception: entity creation where the subject does not
//! yet exist.
//!
//! ## Gas
//!
//! Two-tier: **structural gas** bounded statically by program shape,
//! **extensional gas** metered against runtime cardinality certificates.

#![warn(missing_docs)]
#![warn(unsafe_code)]

pub mod ast;
pub mod effects;
pub mod error;
pub mod gas;
pub mod host;
pub mod parser;
pub mod types;

pub use ast::{
    ApprovalMode, BinOp, CardinalityCertificate, CompensationClause, Contract, Contracts, Effect,
    ExprNode, FailureAction, GasBudget, GovernanceRequirement, MatchArm, OpExpr, OpProgram, OpStep,
    OpType, Outcome, Participant, ParticipantRole, Primitive, ProgramMetadata, SafetyPredicate,
    Statement, StepBody, StepSig, StepSignature, UnOp, WaitSpec,
};
pub use effects::{check_effect_safety, EffectRow, EffectSafetyError};
pub use error::OpError;
pub use gas::{GasConfig, GasEstimate, GasMeter};
pub use host::{HostError, HostOutcome, OpHost, PrimitiveCall};
pub use parser::{parse_program, parse_step};
pub use types::{
    program_effect_row, typecheck_program, GasAnalysis, SafetyPredicateFailure, TypeCheckResult,
    TypeContext,
};
