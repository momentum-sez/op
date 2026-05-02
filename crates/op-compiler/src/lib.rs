//! # op-compiler — Source-language / YAML → Op AST lowering
//!
//! The Op language admits multiple authoring surfaces. YAML operation
//! definitions are the legacy authoring surface; this crate lowers them into
//! typed `OpProgram` values defined by `op-core`.
//!
//! The lowering is deterministic and semantics-preserving. A program that
//! lowers successfully round-trips through the compiled form without
//! structural drift.
//!
//! ## Lowering classes
//!
//! - **Class A** — mechanical round-trip. Examples: `consent.board_resolution`,
//!   `consent.shareholder_vote`, `ownership.create_share_class`.
//! - **Class B** — structurally correct in YAML but materially better as Op
//!   (parameters can be typed, interpolation becomes projection).
//! - **Class C** — requires semantic surface that YAML only approximates
//!   (multi-entity workflows, cross-zone subflows, first-class policy blocks).

#![warn(missing_docs)]

pub mod hash;
pub mod lower;

pub use hash::{content_address, ContentAddress};
pub use lower::{lower_yaml, LoweringError, LoweringReport};

use op_core::{typecheck_program, GasEstimate, OpProgram, TypeCheckResult};
use serde::{Deserialize, Serialize};

/// A fully compiled Op program.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompiledProgram {
    /// The typed program produced by lowering.
    pub program: OpProgram,
    /// Content address of the compiled artifact.
    pub content_address: ContentAddress,
    /// Result of type-checking (always attached).
    pub type_check: TypeCheckResult,
    /// Static gas estimate.
    pub gas_estimate: GasEstimate,
    /// Whether every compositional safety predicate discharged.
    pub safety_verified: bool,
}

/// Compile a YAML operation definition into a typed `OpProgram`.
pub fn compile_yaml(yaml: &str) -> Result<CompiledProgram, LoweringError> {
    let report = lower_yaml(yaml)?;
    let tc = typecheck_program(&report.program);
    if !tc.success {
        return Err(LoweringError::TypeCheckFailed {
            errors: tc.errors.clone(),
        });
    }
    let gas_estimate = GasEstimate {
        structural_gas: tc
            .gas_analysis
            .as_ref()
            .map(|g| g.structural_bound)
            .unwrap_or(0),
        extensional_gas_bound: tc.gas_analysis.as_ref().and_then(|g| g.max_extensional_gas),
        needs_cardinality_cert: tc
            .gas_analysis
            .as_ref()
            .map(|g| g.needs_cardinality_cert)
            .unwrap_or(false),
    };
    let content_address = content_address(&report.program);
    Ok(CompiledProgram {
        program: report.program,
        content_address,
        safety_verified: tc.failed_predicates.is_empty() && tc.deferred_predicates.is_empty(),
        type_check: tc,
        gas_estimate,
    })
}

/// Semantic version of the compiler output format. Bumped whenever the
/// lowering tables change so content addresses invalidate deterministically.
pub const COMPILER_VERSION: &str = "0.1.0";

#[cfg(test)]
mod tests {
    use super::*;

    const TRIVIAL_YAML: &str = r#"
operation: trivial.noop
jurisdiction: _default
version: "1.0.0"
description: "Placeholder for compile tests."
params:
  required: []
  optional: []
steps:
  - id: noop
    type: document.board_minutes
    compliance_domains: []
"#;

    #[test]
    fn compiles_trivial_yaml() {
        let c = compile_yaml(TRIVIAL_YAML).expect("trivial yaml must compile");
        assert_eq!(c.program.name, "trivial.noop");
        assert_eq!(c.program.jurisdiction, "_default");
        assert!(!c.content_address.hex.is_empty());
    }
}
