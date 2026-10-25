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
pub use lower::{lower_yaml, lower_yaml_v1, LoweringError, LoweringReport, LoweringReportV1};

use op_core::{typecheck_program, GasEstimate, OpProgram, ProgramPurposeTag, TypeCheckResult};
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

/// A compiled result together with its exact authored purpose.
///
/// The inner content address identifies only the historical AST bytes.
/// It does not bind this envelope, the purpose, or a signed executable artifact.
#[derive(Debug, Clone, Serialize)]
pub struct CompiledProgramV1 {
    version: u32,
    purpose: ProgramPurposeTag,
    compiled: CompiledProgram,
}

impl CompiledProgramV1 {
    /// Return the exact authored purpose.
    pub fn purpose(&self) -> &ProgramPurposeTag {
        &self.purpose
    }

    /// Return the compiled AST, static checks, and historical content address.
    pub fn compiled(&self) -> &CompiledProgram {
        &self.compiled
    }

    /// Return both the authored purpose and the compiled result.
    pub fn into_parts(self) -> (ProgramPurposeTag, CompiledProgram) {
        (self.purpose, self.compiled)
    }
}

/// Compile a strict version-one YAML envelope without inferring its purpose.
pub fn compile_yaml_v1(yaml: &str) -> Result<CompiledProgramV1, LoweringError> {
    let report = lower_yaml_v1(yaml)?;
    let (purpose, program) = report.program.into_parts();
    Ok(CompiledProgramV1 {
        version: 1,
        purpose,
        compiled: compile_program(program)?,
    })
}

/// Compile a YAML operation definition into a typed `OpProgram`.
pub fn compile_yaml(yaml: &str) -> Result<CompiledProgram, LoweringError> {
    let report = lower_yaml(yaml)?;
    compile_program(report.program)
}

fn compile_program(program: OpProgram) -> Result<CompiledProgram, LoweringError> {
    let tc = typecheck_program(&program);
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
    let content_address =
        content_address(&program).map_err(|e| LoweringError::ContentAddress(e.to_string()))?;
    Ok(CompiledProgram {
        program,
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
