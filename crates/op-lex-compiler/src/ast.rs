//! Minimal `LexTerm` AST — the admissible-fragment subset consumed by the
//! `[[·]] : Lex -> Op` compilation function.
//!
//! The Lex calculus (see the separate Lex repository) is substantially larger
//! than what a compilation target for Op needs: temporal modalities, tribunal
//! modalities, dependent pair types, principle balancing, hole introductions,
//! inductive eliminators at arbitrary levels, and effect-row-carrying
//! pi-types live in the full calculus. The admissible fragment — first-order
//! data, modal-free, temporal-coercion-free, filled-hole-only, and
//! exhaustive-match-only — is a closed proper subset that admits a total
//! compilation to Op.
//!
//! This module vendors the shapes the compiler touches. Callers that already
//! carry a full Lex AST construct these values by translation; callers that
//! only need compilation build them directly. Both patterns keep the Op crate
//! free of a cross-repository path dependency.

use serde::{Deserialize, Serialize};

/// A source location carried forward for diagnostics.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct LexLoc {
    /// Source file identifier.
    pub file: String,
    /// One-based source line.
    pub line: u32,
    /// Zero-based column.
    pub column: u32,
}

/// Base values recognized by the admissible fragment.
///
/// Only first-order data constructors appear: booleans, integers, strings,
/// record literals with named fields, variant literals tagged by a
/// constructor name, lists, and the `None` / `Some` optional constructors.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum LexValue {
    /// Boolean literal.
    Bool(bool),
    /// Integer literal.
    Int(i64),
    /// String literal.
    Str(String),
    /// Record literal with named fields.
    Record(Vec<(String, LexValue)>),
    /// Variant literal: `Tag payload`.
    Variant {
        /// Constructor name.
        tag: String,
        /// Carried payload (unit when none).
        payload: Box<LexValue>,
    },
    /// List literal.
    List(Vec<LexValue>),
    /// Unit literal (`()`), used as the neutral payload.
    Unit,
}

/// A match branch in the admissible fragment.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexBranch {
    /// Constructor the branch matches.
    pub tag: String,
    /// Binder for the destructured payload.
    pub binder: String,
    /// Branch body.
    pub body: LexTerm,
}

/// A defeasible-rule exception.
///
/// Priorities totally order exceptions within a rule: higher priority
/// dominates; ties break on source position ascending.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexException {
    /// Decidable guard proposition.
    pub guard: LexTerm,
    /// Exception body, returning the same type as the rule's base.
    pub body: LexTerm,
    /// Priority — strictly greater overrides strictly lesser.
    pub priority: u32,
    /// Source position for tie-breaking.
    pub source_position: u32,
}

/// A Lex term in the admissible fragment.
///
/// Deliberately omits: temporal modalities (`@`, `◇`, `□`), tribunal
/// modalities (`⟦T⟧`, `coerce`), dependent pair types (`Σ`), principle
/// balancing, unfilled discretion holes, effect-row-carrying pi-types, and
/// arbitrary-level inductive eliminators. The admissibility gate in
/// `admissibility` rejects terms carrying any of those shapes before any
/// compilation case fires.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum LexTerm {
    /// A base value (§6.2 constant case).
    Const(LexValue),

    /// A variable reference. The admissible fragment restricts `Var` to names
    /// already bound in the prelude; other references are rejected.
    Var {
        /// Human-readable name.
        name: String,
        /// De Bruijn index (for downstream consistency).
        index: u32,
    },

    /// A pattern match on a variant scrutinee, with explicit return type.
    Match {
        /// Scrutinee evaluating to a variant.
        scrutinee: Box<LexTerm>,
        /// Branches — one per decidable constructor.
        branches: Vec<LexBranch>,
    },

    /// A defeasible rule with a base body and zero-or-more exceptions.
    Defeasible {
        /// Rule identifier, used for diagnostics.
        name: String,
        /// Base body (fallback when no exception guard fires).
        base: Box<LexTerm>,
        /// Exceptions. Not required to be pre-sorted.
        exceptions: Vec<LexException>,
    },

    /// A sanctions-dominance introduction over a principal term.
    ///
    /// Execution semantics: evaluate the principal, call the host's sanctions
    /// primitive; if sanctioned, emit the verdict `SanctionsBlocked`;
    /// otherwise emit `Compliant`.
    SanctionsDominance {
        /// Principal expression (an entity reference).
        principal: Box<LexTerm>,
    },

    /// A filled discretion hole. Unfilled holes are non-admissible.
    HoleFill {
        /// Hole identifier.
        hole_id: String,
        /// Filler value.
        value: Box<LexTerm>,
        /// Witness (PCAuth digest or equivalent attestation).
        witness: Witness,
    },

    /// A call into the prelude (e.g. `prelude.equals`, `prelude.or`,
    /// `prelude.contains`). The admissibility gate rejects calls whose
    /// callee is not in the prelude binding.
    PreludeCall {
        /// Callee qualified name (must be registered in the prelude).
        callee: String,
        /// Positional arguments.
        args: Vec<LexTerm>,
    },
}

/// Attestation witness carried by a filled hole.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Witness {
    /// Authority identifier (`ofac`, `registry.sez.seychelles`, etc.).
    pub authority: String,
    /// Content digest of the filling act.
    pub digest: String,
    /// Timestamp of the filling, as an RFC 3339 string.
    pub timestamp: String,
}

/// Convenience constructors used by tests and examples.
impl LexTerm {
    /// Construct a boolean constant.
    pub fn const_bool(b: bool) -> Self {
        LexTerm::Const(LexValue::Bool(b))
    }

    /// Construct an integer constant.
    pub fn const_int(i: i64) -> Self {
        LexTerm::Const(LexValue::Int(i))
    }

    /// Construct a string constant.
    pub fn const_string(s: &str) -> Self {
        LexTerm::Const(LexValue::Str(s.to_string()))
    }

    /// Construct a variable reference.
    pub fn var(name: &str, index: u32) -> Self {
        LexTerm::Var {
            name: name.to_string(),
            index,
        }
    }

    /// Construct a sanctions-dominance node over a string principal.
    pub fn sanctions_dominance_of(principal: LexTerm) -> Self {
        LexTerm::SanctionsDominance {
            principal: Box::new(principal),
        }
    }
}
