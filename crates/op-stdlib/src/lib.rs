//! # op-stdlib — Canonical primitive corpus
//!
//! The canonical corpus describes the **shapes** of institutional workflow
//! primitives — entity creation, fiscal transfer, sanctions screening,
//! governance ceremonies, document generation — without binding any specific
//! backend. Host embedders register concrete implementations against these
//! corpus entries.
//!
//! Each `PrimitiveShape` records:
//! - the primitive's dotted identifier (`create.entity`, `fiscal.transfer`, …)
//! - the canonical family it belongs to (Entity, Ownership, Fiscal, Identity,
//!   Consent, Trade, Document, Screening, Governance, Filing)
//! - the default effect row the primitive carries
//! - whether the primitive is deferred-subject (entity-creation class)
//!
//! This crate is deliberately data-only. The primitives here mirror the shape
//! of the reference institutional vocabulary without encoding any backend
//! policy.

#![warn(missing_docs)]

use op_core::{Effect, Primitive};

pub mod canonical;

pub use canonical::{family_of, lookup, PrimitiveFamily, PrimitiveShape, CANONICAL_PRIMITIVES};

/// Return the default effect row the stdlib assigns to a primitive.
pub fn default_effects(primitive: &Primitive) -> Vec<Effect> {
    lookup(&primitive.0)
        .map(|s| s.default_effects.to_vec())
        .unwrap_or_default()
}

/// Return whether a primitive qualifies for the deferred-subject sanctions
/// exception (i.e. entity-creation class, subject does not yet exist).
pub fn is_deferred_subject(primitive: &Primitive) -> bool {
    lookup(&primitive.0)
        .map(|s| s.deferred_subject)
        .unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn entity_create_is_deferred_subject() {
        assert!(is_deferred_subject(&Primitive("create.entity".to_string())));
    }

    #[test]
    fn unknown_primitive_has_no_default_effects() {
        assert!(default_effects(&Primitive("unknown.thing".to_string())).is_empty());
    }

    #[test]
    fn canonical_corpus_is_non_empty() {
        assert!(!CANONICAL_PRIMITIVES.is_empty());
    }
}
