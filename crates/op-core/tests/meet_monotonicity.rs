//! Meet-monotonicity of pointwise compliance-tensor composition.
//!
//! Two compliance tensors `T_A` and `T_B` over a shared domain set
//! `{d1, d2, d3}` compose via pointwise meet on the verdict lattice:
//!
//! ```text
//!   T_AB(d) = T_A(d) ⋀ T_B(φ(d))
//! ```
//!
//! The meet operation `⋀` is a commutative, idempotent, associative
//! operation with a partial order:
//!
//! ```text
//!   Compliant ≤ Partial ≤ NonCompliant ≤ SanctionsBlocked
//! ```
//!
//! Composition monotonicity: for every domain `d`,
//!
//! ```text
//!   T_AB(d) ≥ T_A(d)    and    T_AB(d) ≥ T_B(φ(d))
//! ```
//!
//! This reads: composing tensors can only introduce strictly-greater
//! (more restrictive) verdicts; it can never weaken a constraint. The
//! test exhausts every combination on a 3-domain tensor under identity
//! correspondence `φ(d) = d` and asserts the bound at every domain.

use std::collections::BTreeMap;

/// The verdict lattice. Partial order: lower index = more compliant.
/// `Compliant ≤ Partial ≤ NonCompliant ≤ SanctionsBlocked`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Verdict {
    Compliant,
    Partial,
    NonCompliant,
    SanctionsBlocked,
}

impl Verdict {
    /// Pointwise meet: the greater (more restrictive) of the two. The
    /// compliance-tensor composition uses "meet" in the sense of "the
    /// composition can only worsen or preserve the verdict"; an
    /// equivalent reading is max on the linearly ordered chain.
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

/// A tensor mapping domain identifiers to verdicts.
type Tensor = BTreeMap<String, Verdict>;

fn tensor(d1: Verdict, d2: Verdict, d3: Verdict) -> Tensor {
    let mut t = BTreeMap::new();
    t.insert("d1".to_string(), d1);
    t.insert("d2".to_string(), d2);
    t.insert("d3".to_string(), d3);
    t
}

/// Pointwise meet under identity correspondence `φ(d) = d`.
fn compose(a: &Tensor, b: &Tensor) -> Tensor {
    let mut out = BTreeMap::new();
    for (d, va) in a {
        let vb = b.get(d).copied().expect("shared domain set");
        out.insert(d.clone(), va.meet(vb));
    }
    out
}

#[test]
fn pointwise_meet_dominates_each_operand() {
    // Exhaustive sweep over the 4^3 × 4^3 = 4096 tensor pairs.
    for a1 in Verdict::all() {
        for a2 in Verdict::all() {
            for a3 in Verdict::all() {
                for b1 in Verdict::all() {
                    for b2 in Verdict::all() {
                        for b3 in Verdict::all() {
                            let t_a = tensor(a1, a2, a3);
                            let t_b = tensor(b1, b2, b3);
                            let t_ab = compose(&t_a, &t_b);
                            for d in ["d1", "d2", "d3"] {
                                let ab = *t_ab.get(d).unwrap();
                                let a = *t_a.get(d).unwrap();
                                let b = *t_b.get(d).unwrap();
                                assert!(
                                    ab >= a,
                                    "monotonicity violated: T_AB({d}) = {ab:?} < T_A({d}) = {a:?}"
                                );
                                assert!(
                                    ab >= b,
                                    "monotonicity violated: T_AB({d}) = {ab:?} < T_B({d}) = {b:?}"
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
fn meet_is_commutative_idempotent_associative() {
    for a in Verdict::all() {
        // Idempotent.
        assert_eq!(a.meet(a), a, "meet not idempotent at {a:?}");
        for b in Verdict::all() {
            // Commutative.
            assert_eq!(
                a.meet(b),
                b.meet(a),
                "meet not commutative on ({a:?}, {b:?})"
            );
            for c in Verdict::all() {
                // Associative.
                assert_eq!(
                    a.meet(b).meet(c),
                    a.meet(b.meet(c)),
                    "meet not associative on ({a:?}, {b:?}, {c:?})"
                );
            }
        }
    }
}

#[test]
fn sanctions_blocked_is_the_top() {
    // SanctionsBlocked dominates every other verdict under pointwise
    // composition — consistent with the sanctions-bottom semantics at
    // the language level (sanctions-blocked principals absorb all
    // downstream verdicts).
    for v in Verdict::all() {
        assert_eq!(
            v.meet(Verdict::SanctionsBlocked),
            Verdict::SanctionsBlocked,
            "SanctionsBlocked does not dominate {v:?}"
        );
    }
}
