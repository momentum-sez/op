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

/// Compute the content address of a program.
pub fn content_address(program: &OpProgram) -> ContentAddress {
    let canonical = serde_json::to_string(program).unwrap_or_default();
    let h = fnv1a_64(canonical.as_bytes());
    ContentAddress {
        hash: h,
        hex: format!("{h:016x}"),
        algorithm: "fnv1a-64".to_string(),
    }
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
        let a = content_address(&p);
        let b = content_address(&p);
        assert_eq!(a, b);
    }

    #[test]
    fn content_address_changes_with_body() {
        let p1 = prog_with_body(vec![Statement::Return(OpExpr::Int(1))]);
        let p2 = prog_with_body(vec![Statement::Return(OpExpr::Int(2))]);
        assert_ne!(content_address(&p1).hash, content_address(&p2).hash);
    }
}
