//! Typed errors surfaced by the `[[·]] : Lex -> Op` compilation function.
//!
//! Two error families cover every rejection path: admissibility violations
//! (the input Lex term is outside the fragment the compilation function is
//! total on) and translation failures (the input is admissible but the
//! prelude or context binding is missing).

use crate::ast::LexLoc;
use thiserror::Error;

/// Specific admissibility clauses, matching the admissibility predicate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmissibilityViolation {
    /// Clause (a): non-first-order value detected — function-typed binding,
    /// dependent-pair term, or similarly higher-order shape.
    NotFirstOrder {
        /// Short explanation of what shape was seen.
        detail: String,
    },

    /// Clause (b): a modal operator appeared.
    ModalPresent {
        /// The modal kind (`at`, `eventually`, `always`, `tribunal-intro`,
        /// `tribunal-coerce`).
        modal: String,
    },

    /// Clause (c): a temporal coercion appeared.
    TemporalCoercionPresent,

    /// Clause (d): an unfilled discretion hole appeared.
    UnfilledHole {
        /// Hole identifier.
        hole_id: String,
    },

    /// Clause (e): a match whose exhaustiveness is not decidable by the
    /// prelude (missing branch for some constructor of the scrutinee type,
    /// or open-ended variant).
    ExhaustivenessUndecidable {
        /// Location of the offending match.
        loc: LexLoc,
        /// Detail (e.g. "missing branch for `Individual`").
        detail: String,
    },

    /// Defeasible-rule exceptions fail to form a total order on
    /// `(priority DESC, source_position ASC)`. Two exceptions sharing the
    /// same `(priority, source_position)` pair are observationally
    /// indistinguishable by the defeasible resolution rule, which would
    /// leave the compiled program under-determined.
    DefeasibleOrderNotTotal {
        /// Colliding priority.
        priority: u32,
        /// Colliding source position.
        source_position: u32,
    },
}

/// Compilation failure.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum CompileError {
    /// The input term failed the admissibility predicate.
    #[error("lex term not admissible: {reason:?}")]
    NotAdmissible {
        /// The clause that rejected the term.
        reason: AdmissibilityViolation,
    },

    /// A prelude call names a callee the context does not bind.
    #[error("unsupported prelude call: {name}")]
    UnsupportedPreludeCall {
        /// The callee name.
        name: String,
    },

    /// Match exhaustiveness could not be decided.
    #[error("pattern exhaustiveness undecidable at {loc:?}")]
    PatternExhaustivenessUndecidable {
        /// Source location.
        loc: LexLoc,
    },

    /// An unfilled hole was encountered at the fill-site.
    #[error("unfilled discretion hole: {hole_id}")]
    UnfilledHole {
        /// Hole identifier.
        hole_id: String,
    },

    /// A modal surfaced inside a compilation case (should have been rejected
    /// by the admissibility gate; surfaced for defence-in-depth).
    #[error("modal unsupported: {modal}")]
    ModalUnsupported {
        /// Modal label.
        modal: String,
    },

    /// A temporal coercion surfaced inside a compilation case.
    #[error("temporal coercion unsupported")]
    TemporalCoercion,

    /// A variable reference targeted a name outside the prelude binding.
    #[error("unbound variable: {name}")]
    UnboundVariable {
        /// The name.
        name: String,
    },
}
