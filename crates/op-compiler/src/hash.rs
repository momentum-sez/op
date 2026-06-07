//! Content addressing for compiled Op programs.
//!
//! The content address is the FNV-1a 64-bit hash of the canonical JSON
//! serialization of the program. Canonicalization uses `serde_json`'s
//! default (field ordering as declared in the struct), which is stable as
//! long as the AST types stay stable.
//!
//! The choice of FNV-1a is intentional: it is dependency-free and
//! deterministic across platforms. For cryptographic-strength addressing,
//! a host embedder may replace `content_address` with a BLAKE3 or SHA-256
//! derivation. The Op language does not require cryptographic hashing.

use op_core::OpProgram;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// A content address.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContentAddress {
    /// Raw 64-bit hash.
    pub hash: u64,
    /// Hex-encoded for convenience.
    pub hex: String,
    /// Algorithm identifier (`fnv1a-64` for the reference implementation).
    pub algorithm: String,
}

/// Failure computing a content address.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum ContentAddressError {
    /// The program failed to serialize to its canonical JSON form. The content
    /// address is derived from those bytes, so a serialization failure must
    /// fail loud — hashing the empty string instead would collapse every
    /// unserializable program (and a genuinely-empty one) onto a single,
    /// meaningless content id.
    #[error("program failed to serialize for content addressing: {0}")]
    Serialize(String),
}

/// Compute the content address of a program.
///
/// Fail-loud: serialization failure returns [`ContentAddressError::Serialize`]
/// rather than hashing the empty string. A content id must be a function of the
/// program's real bytes; a silent `""` fallback would make distinct programs
/// share an id.
pub fn content_address(program: &OpProgram) -> Result<ContentAddress, ContentAddressError> {
    let canonical =
        serde_json::to_string(program).map_err(|e| ContentAddressError::Serialize(e.to_string()))?;
    let h = fnv1a_64(canonical.as_bytes());
    Ok(ContentAddress {
        hash: h,
        hex: format!("{h:016x}"),
        algorithm: "fnv1a-64".to_string(),
    })
}

fn fnv1a_64(data: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in data {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01B3);
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;
    use op_core::{Contracts, GasBudget, OpExpr, OpProgram, ProgramMetadata, Statement};

    fn prog_with_body(body: Vec<Statement>) -> OpProgram {
        OpProgram {
            name: "t.op".to_string(),
            jurisdiction: "_default".to_string(),
            metadata: ProgramMetadata::default(),
            inputs: vec![],
            outputs: vec![],
            effects: vec![],
            participants: vec![],
            approval: None,
            contracts: Contracts::default(),
            body,
            gas_budget: GasBudget::default(),
        }
    }

    #[test]
    fn content_address_deterministic() {
        let p = prog_with_body(vec![Statement::Return(OpExpr::Int(1))]);
        let a = content_address(&p).expect("serializes");
        let b = content_address(&p).expect("serializes");
        assert_eq!(a, b);
    }

    #[test]
    fn content_address_changes_with_body() {
        let p1 = prog_with_body(vec![Statement::Return(OpExpr::Int(1))]);
        let p2 = prog_with_body(vec![Statement::Return(OpExpr::Int(2))]);
        assert_ne!(
            content_address(&p1).expect("serializes").hash,
            content_address(&p2).expect("serializes").hash
        );
    }

    #[test]
    fn content_address_never_hashes_empty_string() {
        // The empty-string FNV-1a digest is the value a silent `unwrap_or_default`
        // would have minted on serialize failure. No real program may collide
        // with it: a content id must reflect the program's actual bytes.
        let empty_string_digest = fnv1a_64(b"");
        let p = prog_with_body(vec![Statement::Return(OpExpr::Int(1))]);
        assert_ne!(
            content_address(&p).expect("serializes").hash,
            empty_string_digest
        );
    }
}
