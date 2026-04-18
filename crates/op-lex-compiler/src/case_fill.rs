//! §6.2 fill rule:
//!
//! ```text
//!   [[HoleFill { hole_id, value, witness }]] = [[value]]
//!
//!   with a τ-labelled attestation-append written into the mu trace.
//! ```
//!
//! The attestation append extends Op's `mu` trace but is τ-labelled (silent)
//! per Op §6.3 fill bisimulation case — the trace carries the fact that the
//! hole was filled, but does not itself introduce a verdict. Downstream
//! compensation replays the τ-label during inverse execution.
//!
//! Emission shape: `OpExpr::Seq(attestation_call, value)`. The `Seq` form
//! evaluates the attestation call for its effect (which the host routes to
//! the proof bundle as a `ProofEmit`), discards that return value, then
//! evaluates and returns `value`. This preserves the Op-type of the fill
//! expression as exactly `type_of(value)`, satisfying the §6.3 weak
//! bisimulation equation `[[fill(h, v, w)]] = [[v]]` up to τ-labels on `mu`.

use crate::ast::Witness;
use op_core::OpExpr;

/// Compile a filled hole: emit the attestation call sequenced before the
/// lifted value. The Seq form evaluates the attestation for its effect,
/// then returns the value with its original Op-type intact.
pub fn compile_fill(hole_id: &str, value: OpExpr, witness: &Witness) -> OpExpr {
    let attestation_call = OpExpr::Call(
        "attestation.append".to_string(),
        vec![
            (
                "hole_id".to_string(),
                OpExpr::String(hole_id.to_string()),
            ),
            (
                "authority".to_string(),
                OpExpr::String(witness.authority.clone()),
            ),
            (
                "digest".to_string(),
                OpExpr::String(witness.digest.clone()),
            ),
            (
                "timestamp".to_string(),
                OpExpr::String(witness.timestamp.clone()),
            ),
        ],
    );
    // §6.2: [[fill(h, v, w)]] = [[v]], with w persisted as τ-labelled
    // attestation append into the proof bundle. Seq evaluates the
    // attestation call for its effect, then returns the value with its
    // original type.
    OpExpr::Seq(Box::new(attestation_call), Box::new(value))
}
