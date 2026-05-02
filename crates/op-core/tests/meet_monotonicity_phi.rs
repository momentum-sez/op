//! Meet-monotonicity under a non-identity domain correspondence φ.
//!
//! Paper reference: "Op: A Typed Effectful Workflow Language" §5.5
//! "Meet-monotonicity with non-identity φ".
//!
//! The existing `meet_monotonicity.rs` test exercises the identity
//! case `φ(d) = d` — `T_AB(d) = T_A(d) ⋀ T_B(d)`. The paper's stronger
//! claim holds under any corridor correspondence φ: a permutation, an
//! inclusion, or any domain-level mapping of φ: D → D that the bilateral
//! agreement declares.
//!
//! Concretely, for every domain `d` in the shared domain set:
//!
//! ```text
//!   T_AB(d) ≥ T_A(d)    and    T_AB(d) ≥ T_B(φ(d))
//! ```
//!
//! reading ≥ on the verdict chain as "more restrictive or equal". The
//! test exercises the non-trivial cyclic permutation
//!
//! ```text
//!   φ(d1) = d2
//!   φ(d2) = d3
//!   φ(d3) = d1
//! ```
//!
//! and sweeps exhaustively over all `4^3 × 4^3 = 4096` tensor pairs,
//! asserting both bounds at every domain. A secondary test covers
//! every permutation of the three domains to show the claim does not
//! depend on the specific cycle chosen.

use std::collections::BTreeMap;

/// Verdict lattice identical to `meet_monotonicity.rs`.
/// Compliant ≤ Partial ≤ NonCompliant ≤ SanctionsBlocked.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Verdict {
    Compliant,
    Partial,
    NonCompliant,
    SanctionsBlocked,
}

impl Verdict {
    fn meet(self, other: Verdict) -> Verdict {
        if self >= other {
            self
        } else {
            other
        }
    }

    fn all() -> [Verdict; 4] {
        [
            Verdict::Compliant,
            Verdict::Partial,
            Verdict::NonCompliant,
            Verdict::SanctionsBlocked,
        ]
    }
}

type Tensor = BTreeMap<String, Verdict>;

fn tensor(d1: Verdict, d2: Verdict, d3: Verdict) -> Tensor {
    let mut t = BTreeMap::new();
    t.insert("d1".to_string(), d1);
    t.insert("d2".to_string(), d2);
    t.insert("d3".to_string(), d3);
    t
}

/// A domain correspondence φ: D → D as an ordinary map.
fn compose_with_phi<F>(a: &Tensor, b: &Tensor, phi: F) -> Tensor
where
    F: Fn(&str) -> &'static str,
{
    let mut out = BTreeMap::new();
    for (d, va) in a {
        let phi_d = phi(d.as_str());
        let vb = b
            .get(phi_d)
            .copied()
            .expect("correspondence must land inside the shared domain set");
        out.insert(d.clone(), va.meet(vb));
    }
    out
}

/// The cyclic permutation `φ(d1) = d2, φ(d2) = d3, φ(d3) = d1`.
fn phi_cycle(d: &str) -> &'static str {
    match d {
        "d1" => "d2",
        "d2" => "d3",
        "d3" => "d1",
        other => panic!("unknown domain: {other}"),
    }
}

#[test]
fn pointwise_meet_dominates_each_operand_under_cyclic_phi() {
    // Exhaustive sweep. For every tensor pair and every domain d, the
    // meet under φ must dominate both sides: the A-tensor's verdict at
    // d, AND the B-tensor's verdict at φ(d). The second bound is what
    // the non-identity case adds; it is the paper's load-bearing claim
    // for corridors that re-label compliance domains across zones.
    for a1 in Verdict::all() {
        for a2 in Verdict::all() {
            for a3 in Verdict::all() {
                for b1 in Verdict::all() {
                    for b2 in Verdict::all() {
                        for b3 in Verdict::all() {
                            let t_a = tensor(a1, a2, a3);
                            let t_b = tensor(b1, b2, b3);
                            let t_ab = compose_with_phi(&t_a, &t_b, phi_cycle);
                            for d in ["d1", "d2", "d3"] {
                                let ab = *t_ab.get(d).unwrap();
                                let a = *t_a.get(d).unwrap();
                                let phi_d = phi_cycle(d);
                                let b_phi = *t_b.get(phi_d).unwrap();
                                assert!(
                                    ab >= a,
                                    "bound A violated: T_AB({d}) = {ab:?} < T_A({d}) = {a:?}"
                                );
                                assert!(
                                    ab >= b_phi,
                                    "bound B violated: T_AB({d}) = {ab:?} < T_B(φ({d})) = T_B({phi_d}) = {b_phi:?}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn meet_monotonicity_holds_for_every_permutation_of_three_domains() {
    // The cyclic case is one of six permutations. The bound must hold
    // for each — the claim is universal across φ, not a property of
    // the specific mapping used above.
    let permutations: &[[&str; 3]] = &[
        ["d1", "d2", "d3"], // identity
        ["d1", "d3", "d2"], // swap d2 and d3
        ["d2", "d1", "d3"], // swap d1 and d2
        ["d2", "d3", "d1"], // cyclic forward
        ["d3", "d1", "d2"], // cyclic backward
        ["d3", "d2", "d1"], // reverse
    ];

    // Run a smaller sweep per permutation to keep runtime reasonable:
    // the exhaustive-domain check is already handled by the cyclic test
    // above. Here the goal is to hit every permutation with a few
    // representative values each.
    let probes = [
        (Verdict::Compliant, Verdict::Partial, Verdict::NonCompliant),
        (
            Verdict::Partial,
            Verdict::SanctionsBlocked,
            Verdict::Compliant,
        ),
        (
            Verdict::SanctionsBlocked,
            Verdict::Compliant,
            Verdict::Partial,
        ),
    ];

    // Build a concrete φ for each permutation. Use `&'static str` both
    // for domain names and for the image, so the closure signature
    // matches the helper `compose_with_phi` expects.
    fn make_phi(perm: [&'static str; 3]) -> impl Fn(&str) -> &'static str {
        move |d: &str| -> &'static str {
            match d {
                "d1" => perm[0],
                "d2" => perm[1],
                "d3" => perm[2],
                other => panic!("unknown domain: {other}"),
            }
        }
    }

    for perm in permutations {
        for (a1, a2, a3) in probes {
            for (b1, b2, b3) in probes {
                let t_a = tensor(a1, a2, a3);
                let t_b = tensor(b1, b2, b3);
                let phi = make_phi(*perm);
                let t_ab = compose_with_phi(&t_a, &t_b, &phi);
                for d in ["d1", "d2", "d3"] {
                    let ab = *t_ab.get(d).unwrap();
                    let a = *t_a.get(d).unwrap();
                    let phi_d = phi(d);
                    let b_phi = *t_b.get(phi_d).unwrap();
                    assert!(
                        ab >= a,
                        "permutation {perm:?}: bound A violated at {d}: {ab:?} < {a:?}"
                    );
                    assert!(
                        ab >= b_phi,
                        "permutation {perm:?}: bound B violated at {d}: {ab:?} < T_B({phi_d}) = {b_phi:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn phi_cycle_returns_bounds_consistent_with_identity_at_fixed_points() {
    // Sanity: if an entry happens to be a fixed point of the
    // permutation, the identity bound is recovered. The cyclic
    // permutation above has NO fixed points, so there are no
    // coincidences hiding the bound — the claim genuinely bites.
    let domains = ["d1", "d2", "d3"];
    for d in domains {
        assert_ne!(
            phi_cycle(d),
            d,
            "phi_cycle should have no fixed points; {d} maps to itself, masking the non-identity case"
        );
    }
}

#[test]
fn non_identity_phi_can_produce_different_composite_than_identity() {
    // Existence proof: there is a tensor pair whose identity-composite
    // differs from its φ-composite. Without this, the non-identity case
    // would be vacuous. The witness locks in that the paper's extended
    // claim is non-degenerate.
    let t_a = tensor(
        Verdict::Compliant,
        Verdict::SanctionsBlocked,
        Verdict::Compliant,
    );
    let t_b = tensor(
        Verdict::SanctionsBlocked,
        Verdict::Compliant,
        Verdict::Compliant,
    );

    fn identity_phi(d: &str) -> &'static str {
        match d {
            "d1" => "d1",
            "d2" => "d2",
            "d3" => "d3",
            other => panic!("unknown domain: {other}"),
        }
    }
    let identity = compose_with_phi(&t_a, &t_b, identity_phi);
    let permuted = compose_with_phi(&t_a, &t_b, phi_cycle);

    assert_ne!(
        identity, permuted,
        "non-identity φ should generally differ from identity composition"
    );

    // Still must satisfy the bound under the permuted correspondence.
    for d in ["d1", "d2", "d3"] {
        let ab = *permuted.get(d).unwrap();
        assert!(ab >= *t_a.get(d).unwrap());
        assert!(ab >= *t_b.get(phi_cycle(d)).unwrap());
    }
}
