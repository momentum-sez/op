//! §6.2 fill rule:
//!
//! ```text
//!   [[HoleFill { hole_id, value, witness }]] =
//!     call("attestation.append", { hole_id, witness });
//!     [[value]]
//! ```
//!
//! The attestation append extends Op's `mu` trace but is τ-labelled (silent)
//! per Op §6.3 fill bisimulation case — the trace carries the fact that the
//! hole was filled, but does not itself introduce a verdict. Downstream
//! compensation replays the τ-label during inverse execution.
//!
//! Emission shape: a sequence of two statements — the attestation append as
//! an effectful `Run` (because it extends `mu`), and a `Return` of the lifted
//! value. For expression contexts, the emission is an `OpExpr::Call` for the
//! attestation followed by the value, combined with the coalesce operator
//! which preserves the value while ensuring the attestation call's side
//! effect materializes in the evaluation trace.

use crate::ast::Witness;
use op_core::OpExpr;

/// Compile a filled hole: emit the attestation call paired with the value.
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
    // `coalesce(value, attestation_call)` evaluates attestation_call only
    // when value is null. To keep both evaluated deterministically, wrap
    // them in a record whose first field is the effect and whose second
    // field is the result — downstream reads `result`.
    OpExpr::Record(vec![
        ("attestation".to_string(), attestation_call),
        ("result".to_string(), value),
    ])
}
