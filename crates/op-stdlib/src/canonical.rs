//! Canonical primitive corpus.
//!
//! Each entry records the shape of one primitive family. The effect column
//! follows the effect-inference table in the Op language spec.

use op_core::Effect;

/// The family a primitive belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveFamily {
    /// Entity primitives (create, rename, status updates).
    Entity,
    /// Ownership primitives (share issuance, transfer, membership).
    Ownership,
    /// Fiscal primitives (account open, transfer, treasury).
    Fiscal,
    /// Identity primitives (verify, attest).
    Identity,
    /// Consent primitives (board resolution, shareholder vote, regulatory approval).
    Consent,
    /// Trade primitives (invoice, letter of credit, bill of lading).
    Trade,
    /// Document primitives (minutes, certificates, receipts).
    Document,
    /// Screening primitives (sanctions, PEP, adverse-media).
    Screening,
    /// Registry / filing primitives.
    Filing,
    /// Governance-adjacent primitives.
    Governance,
    /// Update / mutation primitives that don't fit elsewhere.
    Update,
}

/// A canonical primitive shape.
///
/// The corpus is **single-sourced against op-core**: a `PrimitiveShape` records
/// only the stdlib-owned facets — the dotted `name` and its `family`. The
/// default effect row and the deferred-subject flag are NOT stored here; they
/// are derived on demand from op-core's authoritative canonical table
/// ([`op_core::effects::canonical_effects_for`] /
/// [`op_core::effects::canonical_is_deferred_subject`]) so the two crates cannot
/// drift. `op_core` is the single source of truth for effects + the
/// sanctions-domination exemption set; op-stdlib owns the name↔family map.
#[derive(Debug, Clone)]
pub struct PrimitiveShape {
    /// Dotted identifier.
    pub name: &'static str,
    /// Family.
    pub family: PrimitiveFamily,
}

impl PrimitiveShape {
    /// The default effect row, derived from op-core's canonical table.
    /// op-core is the single source of truth; this never invents a row.
    pub fn default_effects(&self) -> Vec<Effect> {
        op_core::effects::canonical_effects_for(self.name)
    }

    /// Whether the primitive is deferred-subject (sanctions check is permitted
    /// to run post-flight), derived from op-core's single canonical predicate.
    pub fn deferred_subject(&self) -> bool {
        op_core::effects::canonical_is_deferred_subject(self.name)
    }
}

/// The canonical corpus (name↔family map).
///
/// Each row mirrors the reference vocabulary visible in the live kernel corpus.
/// Every name here MUST be a primitive op-core's canonical effect table
/// recognizes; the effect row and deferred-subject flag for each are derived
/// from op-core (see [`PrimitiveShape`]). The `stdlib_*` parity tests in `lib.rs`
/// bind this set to op-core in both directions.
pub const CANONICAL_PRIMITIVES: &[PrimitiveShape] = &[
    // Entity
    PrimitiveShape {
        name: "create.entity",
        family: PrimitiveFamily::Entity,
    },
    PrimitiveShape {
        name: "update.entity_status",
        family: PrimitiveFamily::Entity,
    },
    // Ownership
    PrimitiveShape {
        name: "ownership.issue_shares",
        family: PrimitiveFamily::Ownership,
    },
    PrimitiveShape {
        name: "ownership.transfer",
        family: PrimitiveFamily::Ownership,
    },
    PrimitiveShape {
        name: "update.cap_table",
        family: PrimitiveFamily::Ownership,
    },
    PrimitiveShape {
        name: "membership.admit",
        family: PrimitiveFamily::Ownership,
    },
    // Fiscal
    PrimitiveShape {
        name: "create.treasury",
        family: PrimitiveFamily::Fiscal,
    },
    PrimitiveShape {
        name: "create.bank_account",
        family: PrimitiveFamily::Fiscal,
    },
    PrimitiveShape {
        name: "fiscal.open_account",
        family: PrimitiveFamily::Fiscal,
    },
    PrimitiveShape {
        name: "fiscal.transfer",
        family: PrimitiveFamily::Fiscal,
    },
    // Identity
    PrimitiveShape {
        name: "identity.verify",
        family: PrimitiveFamily::Identity,
    },
    // Consent / Governance
    PrimitiveShape {
        name: "consent.board_resolution",
        family: PrimitiveFamily::Consent,
    },
    PrimitiveShape {
        name: "consent.member_resolution",
        family: PrimitiveFamily::Consent,
    },
    PrimitiveShape {
        name: "consent.shareholder_vote",
        family: PrimitiveFamily::Consent,
    },
    // Screening
    PrimitiveShape {
        name: "screening.sanctions",
        family: PrimitiveFamily::Screening,
    },
    // `sanctions.check` is the alias op-core pairs with `screening.sanctions`
    // (same SanctionsCheck + ExternalRead row). It is part of the canonical
    // corpus so the stdlib advertisement matches op-core's recognized set.
    PrimitiveShape {
        name: "sanctions.check",
        family: PrimitiveFamily::Screening,
    },
    // Trade
    PrimitiveShape {
        name: "trade.invoice_create",
        family: PrimitiveFamily::Trade,
    },
    PrimitiveShape {
        name: "trade.lc_issue",
        family: PrimitiveFamily::Trade,
    },
    // Document
    PrimitiveShape {
        name: "document.board_minutes",
        family: PrimitiveFamily::Document,
    },
    PrimitiveShape {
        name: "document.shareholder_minutes",
        family: PrimitiveFamily::Document,
    },
    PrimitiveShape {
        name: "document.commercial_invoice",
        family: PrimitiveFamily::Document,
    },
    // Filing
    PrimitiveShape {
        name: "filing.registry_amendment",
        family: PrimitiveFamily::Filing,
    },
    // Attestation — ProofEmit only; successful append is tau-labelled, failed
    // persistence fails closed (op-core effects.rs).
    PrimitiveShape {
        name: "attestation.append",
        family: PrimitiveFamily::Governance,
    },
    PrimitiveShape {
        name: "attestation.emit",
        family: PrimitiveFamily::Governance,
    },
];

/// Look up a primitive shape by name.
pub fn lookup(name: &str) -> Option<&'static PrimitiveShape> {
    CANONICAL_PRIMITIVES.iter().find(|p| p.name == name)
}

/// Return the family of a primitive, if known.
pub fn family_of(name: &str) -> Option<PrimitiveFamily> {
    lookup(name).map(|p| p.family)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lookup_known_primitive() {
        let p = lookup("create.entity").unwrap();
        assert_eq!(p.family, PrimitiveFamily::Entity);
        assert!(p.deferred_subject());
    }

    #[test]
    fn lookup_unknown_returns_none() {
        assert!(lookup("not.a.primitive").is_none());
    }

    #[test]
    fn family_of_known() {
        assert_eq!(family_of("trade.lc_issue"), Some(PrimitiveFamily::Trade));
    }

    #[test]
    fn every_primitive_has_effects_except_document_generation_only() {
        for p in CANONICAL_PRIMITIVES {
            if p.family == PrimitiveFamily::Document {
                assert!(p
                    .default_effects()
                    .iter()
                    .any(|e| *e == Effect::DocumentGeneration));
            } else {
                assert!(
                    !p.default_effects().is_empty(),
                    "primitive {} has no effects",
                    p.name
                );
            }
        }
    }
}
