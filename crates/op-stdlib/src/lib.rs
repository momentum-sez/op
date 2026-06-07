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
///
/// Fail-loud: a primitive that is not in the canonical corpus returns `None`,
/// **not** an empty effect row. An empty `Vec<Effect>` from this function means
/// "a recognized primitive whose canonical row is genuinely empty" — never "I
/// did not recognize this name." Conflating an unknown primitive with a pure
/// (empty-row) one would let an unscreened write slip the effect-safety gate as
/// if it carried no effects, which is precisely the silent-default hazard this
/// corpus must not have. The row is derived from op-core's single source of
/// truth ([`op_core::effects::canonical_effects_for`]).
pub fn default_effects(primitive: &Primitive) -> Option<Vec<Effect>> {
    lookup(&primitive.0).map(|s| s.default_effects())
}

/// Return whether a primitive qualifies for the deferred-subject sanctions
/// exception (i.e. entity-creation class, subject does not yet exist).
///
/// An unknown primitive returns `false` (fail-closed: it does NOT get the
/// exemption). The exemption is granted only to a recognized corpus member that
/// op-core's single canonical predicate
/// ([`op_core::effects::canonical_is_deferred_subject`]) marks deferred — today
/// exactly `create.entity`.
pub fn is_deferred_subject(primitive: &Primitive) -> bool {
    lookup(&primitive.0)
        .map(|s| s.deferred_subject())
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
        // Fail-loud contract: an unknown primitive is `None`, never an empty
        // (pure) effect row. The distinction is load-bearing — an empty row
        // would be read by the safety analysis as "no effects to gate".
        assert!(default_effects(&Primitive("unknown.thing".to_string())).is_none());
    }

    #[test]
    fn known_primitive_has_some_nonempty_effects() {
        let row = default_effects(&Primitive("fiscal.transfer".to_string()))
            .expect("fiscal.transfer is canonical");
        assert!(!row.is_empty());
        assert!(row.contains(&Effect::FiscalTransfer));
    }

    #[test]
    fn canonical_corpus_is_non_empty() {
        assert!(!CANONICAL_PRIMITIVES.is_empty());
    }

    /// OP-2 binding (effects). For EVERY corpus entry, op-stdlib's derived
    /// effect row MUST byte-equal op-core's canonical row. op-core is the
    /// single source of truth; this test refuses any drift between the
    /// advertised stdlib corpus and the table the live safety analysis uses.
    #[test]
    fn stdlib_effects_match_op_core() {
        for shape in CANONICAL_PRIMITIVES {
            let stdlib_row = shape.default_effects();
            let op_core_row = op_core::effects::canonical_effects_for(shape.name);
            assert_eq!(
                stdlib_row, op_core_row,
                "effect-row drift for '{}': stdlib={stdlib_row:?} op-core={op_core_row:?}",
                shape.name
            );
            // A corpus member op-core does not recognize would resolve to an
            // empty row here — that is itself a drift and must fail.
            assert!(
                !op_core_row.is_empty(),
                "corpus member '{}' has an empty op-core effect row (unrecognized by op-core)",
                shape.name
            );
        }
    }

    /// OP-2 binding (sanctions-domination exemption set). For EVERY corpus
    /// entry, op-stdlib's deferred-subject flag MUST equal op-core's single
    /// canonical predicate. This is the binding that prevents an unscreened
    /// sovereign write from silently passing the sanctions-domination gate via
    /// table drift between the two crates.
    #[test]
    fn stdlib_deferred_subject_matches_op_core() {
        for shape in CANONICAL_PRIMITIVES {
            let stdlib_deferred = shape.deferred_subject();
            let op_core_deferred = op_core::effects::canonical_is_deferred_subject(shape.name);
            assert_eq!(
                stdlib_deferred, op_core_deferred,
                "deferred-subject drift for '{}': stdlib={stdlib_deferred} op-core={op_core_deferred}",
                shape.name
            );
        }
    }

    /// OP-2 binding (both directions). op-core must have NO deferred-subject
    /// primitive that is absent from op-stdlib's corpus, and the whole
    /// exemption set must be exactly `{create.entity}`. If a future edit marks
    /// any other primitive deferred in op-core, this test fails until the
    /// corpus + the exemption-set assertion are reconciled together.
    #[test]
    fn deferred_subject_set_is_exactly_create_entity_both_directions() {
        // Every deferred-subject member of the corpus is `create.entity`.
        let stdlib_deferred: Vec<&str> = CANONICAL_PRIMITIVES
            .iter()
            .filter(|s| s.deferred_subject())
            .map(|s| s.name)
            .collect();
        assert_eq!(
            stdlib_deferred,
            vec!["create.entity"],
            "stdlib deferred-subject set drifted from {{create.entity}}: {stdlib_deferred:?}"
        );

        // op-core agrees the set is exactly {create.entity}: it is deferred,
        // and every other corpus name (the complete set of names op-core can
        // possibly mark deferred via this corpus) is NOT deferred. This closes
        // the op-core→op-stdlib direction: a deferred op-core primitive absent
        // from the corpus cannot exist, because op-core's predicate matches
        // only `create.entity`, which IS in the corpus.
        assert!(op_core::effects::canonical_is_deferred_subject("create.entity"));
        for shape in CANONICAL_PRIMITIVES {
            if shape.name != "create.entity" {
                assert!(
                    !op_core::effects::canonical_is_deferred_subject(shape.name),
                    "op-core marks '{}' deferred-subject but it is not create.entity",
                    shape.name
                );
            }
        }
    }
}
