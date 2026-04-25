//! Terminal set of program evaluation — seven variants.
//!
//! Paper reference: "Op: A Typed Effectful Workflow Language" §4.13.
//!
//! The terminal set enumerates every shape a reduction can take when a
//! typed initial configuration runs under a finite gas budget. The paper
//! fixes the cardinality at seven:
//!
//! 1. Value — reduction completed.
//! 2. Paused — suspended on a callback event.
//! 3. Halted — non-gas, non-sanctions runtime abort.
//! 4. SanctionsBlocked — sanctions gate rejected the principal.
//! 5. OutOfStructuralGas — static structural-gas budget exhausted.
//! 6. OutOfCompensationGas — compensation reserve exhausted during inverse.
//! 7. Timeout — `await` passed its declared `within` duration.
//!
//! This test encodes the invariant directly: a non-default exhaustive
//! match on `Outcome` covers exactly these seven patterns. If the language
//! ever grows or shrinks a variant, the match stops compiling and this
//! test fails to build — the paper and the implementation lose coherence
//! at the earliest possible moment.
//!
//! The serde round-trip cases also check that variant names remain the
//! snake-case tags the paper uses when it cites outcomes in prose; a
//! renaming at the implementation side that silently drifts the public
//! wire format is caught here.

use op_core::Outcome;

/// An exhaustive match function — the compiler rejects this source if
/// any variant is added or removed. Returning the paper's canonical tag
/// doubles the test's load: it pins both the cardinality (seven) and
/// the ordered enumeration (paper §4.13).
fn paper_tag(o: &Outcome) -> &'static str {
    match o {
        Outcome::Value(_) => "value",
        Outcome::Paused { .. } => "paused",
        Outcome::Halted { .. } => "halted",
        Outcome::SanctionsBlocked { .. } => "sanctions_blocked",
        Outcome::OutOfStructuralGas { .. } => "out_of_structural_gas",
        Outcome::OutOfCompensationGas { .. } => "out_of_compensation_gas",
        Outcome::Timeout { .. } => "timeout",
    }
}

fn witnesses() -> Vec<Outcome> {
    vec![
        Outcome::Value(serde_json::json!({"ok": true})),
        Outcome::Paused {
            event: "consent.approved".to_string(),
            resume_token: "tok-1".to_string(),
        },
        Outcome::Halted {
            reason: "host permanent failure".to_string(),
        },
        Outcome::SanctionsBlocked {
            principal: "entity:42".to_string(),
        },
        Outcome::OutOfStructuralGas {
            used: 101,
            limit: 100,
        },
        Outcome::OutOfCompensationGas {
            used: 51,
            limit: 50,
        },
        Outcome::Timeout {
            event: "signature.collected".to_string(),
            timeout_secs: 86_400,
        },
    ]
}

#[test]
fn outcome_set_matches_paper_enumeration() {
    // The paper enumerates exactly seven terminals. A constructor sample
    // per variant must exist; the exhaustive match inside `paper_tag`
    // guarantees no extra variant exists.
    let ws = witnesses();
    assert_eq!(
        ws.len(),
        7,
        "paper §4.13 fixes the terminal set at 7 variants; found {} witnesses",
        ws.len()
    );

    // Every canonical tag is reported by the match arm. Pinning tags
    // catches a rename drift that would otherwise pass a cardinality
    // check silently.
    let expected = [
        "value",
        "paused",
        "halted",
        "sanctions_blocked",
        "out_of_structural_gas",
        "out_of_compensation_gas",
        "timeout",
    ];
    let got: Vec<&str> = ws.iter().map(paper_tag).collect();
    assert_eq!(
        got, expected,
        "paper tags disagree; variants may have been reordered"
    );

    // All seven tags must be distinct — degeneracy would hide a merge of
    // two variants behind one pattern arm.
    let mut uniq: Vec<&str> = got.clone();
    uniq.sort_unstable();
    uniq.dedup();
    assert_eq!(uniq.len(), 7, "paper tags are not distinct: {uniq:?}");
}

#[test]
fn outcome_serde_roundtrip_preserves_paper_tags() {
    // The wire format uses snake_case tags matching the paper's prose.
    // A round-trip confirms the public surface carries the same names a
    // human reader expects when citing §4.13.
    for outcome in witnesses() {
        let json = serde_json::to_string(&outcome).expect("serialize");
        let back: Outcome = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(outcome, back, "round-trip mismatch for {outcome:?}");
    }
}

#[test]
fn outcome_terminal_tags_are_snake_case() {
    // The serde tag on each outcome should render as the snake-case form
    // of its variant — that is the tag the paper uses in prose. This
    // guards against a lower-level `rename_all` drift.
    let pairs = [
        (Outcome::Value(serde_json::Value::Null), "value"),
        (
            Outcome::Paused {
                event: "e".into(),
                resume_token: "t".into(),
            },
            "paused",
        ),
        (Outcome::Halted { reason: "x".into() }, "halted"),
        (
            Outcome::SanctionsBlocked {
                principal: "p".into(),
            },
            "sanctions_blocked",
        ),
        (
            Outcome::OutOfStructuralGas { used: 1, limit: 0 },
            "out_of_structural_gas",
        ),
        (
            Outcome::OutOfCompensationGas { used: 1, limit: 0 },
            "out_of_compensation_gas",
        ),
        (
            Outcome::Timeout {
                event: "e".into(),
                timeout_secs: 1,
            },
            "timeout",
        ),
    ];
    for (outcome, expected_tag) in pairs {
        let v = serde_json::to_value(&outcome).expect("serialize");
        let tag_present = match &v {
            serde_json::Value::Object(m) => m.contains_key(expected_tag),
            serde_json::Value::String(s) => s == expected_tag,
            _ => false,
        };
        assert!(
            tag_present,
            "expected serde tag {expected_tag} in {v:?} for {outcome:?}"
        );
    }
}
