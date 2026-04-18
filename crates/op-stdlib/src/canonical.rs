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
#[derive(Debug, Clone)]
pub struct PrimitiveShape {
    /// Dotted identifier.
    pub name: &'static str,
    /// Family.
    pub family: PrimitiveFamily,
    /// Default effects.
    pub default_effects: &'static [Effect],
    /// Whether the primitive is deferred-subject (sanctions check is
    /// permitted to run post-flight).
    pub deferred_subject: bool,
}

/// The canonical corpus.
///
/// Each row mirrors the reference vocabulary visible in the live kernel
/// corpus and reflects the effect-inference table in the language spec.
pub const CANONICAL_PRIMITIVES: &[PrimitiveShape] = &[
    // Entity
    PrimitiveShape {
        name: "create.entity",
        family: PrimitiveFamily::Entity,
        default_effects: &[Effect::SovereignWrite],
        deferred_subject: true,
    },
    PrimitiveShape {
        name: "update.entity_status",
        family: PrimitiveFamily::Entity,
        default_effects: &[Effect::SovereignWrite],
        deferred_subject: false,
    },
    // Ownership
    PrimitiveShape {
        name: "ownership.issue_shares",
        family: PrimitiveFamily::Ownership,
        default_effects: &[Effect::SovereignWrite],
        deferred_subject: false,
    },
    PrimitiveShape {
        name: "ownership.transfer",
        family: PrimitiveFamily::Ownership,
        default_effects: &[Effect::SovereignWrite],
        deferred_subject: false,
    },
    PrimitiveShape {
        name: "update.cap_table",
        family: PrimitiveFamily::Ownership,
        default_effects: &[Effect::SovereignWrite],
        deferred_subject: false,
    },
    PrimitiveShape {
        name: "membership.admit",
        family: PrimitiveFamily::Ownership,
        default_effects: &[Effect::SovereignWrite],
        deferred_subject: false,
    },
    // Fiscal
    PrimitiveShape {
        name: "create.treasury",
        family: PrimitiveFamily::Fiscal,
        default_effects: &[Effect::SovereignWrite],
        deferred_subject: false,
    },
    PrimitiveShape {
        name: "create.bank_account",
        family: PrimitiveFamily::Fiscal,
        default_effects: &[Effect::SovereignWrite],
        deferred_subject: false,
    },
    PrimitiveShape {
        name: "fiscal.open_account",
        family: PrimitiveFamily::Fiscal,
        default_effects: &[Effect::SovereignWrite],
        deferred_subject: false,
    },
    PrimitiveShape {
        name: "fiscal.transfer",
        family: PrimitiveFamily::Fiscal,
        default_effects: &[Effect::FiscalTransfer, Effect::SovereignWrite],
        deferred_subject: false,
    },
    // Identity
    PrimitiveShape {
        name: "identity.verify",
        family: PrimitiveFamily::Identity,
        default_effects: &[Effect::ExternalRead, Effect::IdentityMutation],
        deferred_subject: false,
    },
    // Consent / Governance
    PrimitiveShape {
        name: "consent.board_resolution",
        family: PrimitiveFamily::Consent,
        default_effects: &[
            Effect::GovernanceRequest,
            Effect::SovereignWrite,
        ],
        deferred_subject: false,
    },
    PrimitiveShape {
        name: "consent.member_resolution",
        family: PrimitiveFamily::Consent,
        default_effects: &[
            Effect::GovernanceRequest,
            Effect::SovereignWrite,
        ],
        deferred_subject: false,
    },
    PrimitiveShape {
        name: "consent.shareholder_vote",
        family: PrimitiveFamily::Consent,
        default_effects: &[
            Effect::GovernanceRequest,
            Effect::SovereignWrite,
        ],
        deferred_subject: false,
    },
    // Screening
    PrimitiveShape {
        name: "screening.sanctions",
        family: PrimitiveFamily::Screening,
        default_effects: &[Effect::SanctionsCheck, Effect::ExternalRead],
        deferred_subject: false,
    },
    // Trade
    PrimitiveShape {
        name: "trade.invoice_create",
        family: PrimitiveFamily::Trade,
        default_effects: &[Effect::FiscalTransfer, Effect::SovereignWrite],
        deferred_subject: false,
    },
    PrimitiveShape {
        name: "trade.lc_issue",
        family: PrimitiveFamily::Trade,
        default_effects: &[Effect::FiscalTransfer, Effect::SovereignWrite],
        deferred_subject: false,
    },
    // Document
    PrimitiveShape {
        name: "document.board_minutes",
        family: PrimitiveFamily::Document,
        default_effects: &[Effect::DocumentGeneration],
        deferred_subject: false,
    },
    PrimitiveShape {
        name: "document.shareholder_minutes",
        family: PrimitiveFamily::Document,
        default_effects: &[Effect::DocumentGeneration],
        deferred_subject: false,
    },
    PrimitiveShape {
        name: "document.commercial_invoice",
        family: PrimitiveFamily::Document,
        default_effects: &[Effect::DocumentGeneration],
        deferred_subject: false,
    },
    // Filing
    PrimitiveShape {
        name: "filing.registry_amendment",
        family: PrimitiveFamily::Filing,
        default_effects: &[Effect::SovereignWrite, Effect::ProofEmit],
        deferred_subject: false,
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
        assert!(p.deferred_subject);
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
                assert!(p.default_effects.iter().any(|e| *e == Effect::DocumentGeneration));
            } else {
                assert!(!p.default_effects.is_empty(), "primitive {} has no effects", p.name);
            }
        }
    }
}
