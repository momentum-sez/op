//! Host-abstraction trait.
//!
//! Op is a language and VM. Concrete behavior for primitives — entity
//! creation, fiscal transfer, sanctions screening, document generation, and
//! so on — lives in the embedding host. This module describes the minimum
//! surface the host must provide.
//!
//! The design intent is explicit: Op ships a deterministic evaluator and a
//! type / effect / gas system. Every side effect flows through the host
//! trait. An embedder can run Op programs against in-memory mocks (for
//! tests), against a full sovereign kernel (for production), or against any
//! backend that implements `OpHost`.

use crate::ast::{Primitive, SafetyPredicate};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use thiserror::Error;

/// Error surfaced by the host during primitive invocation.
#[derive(Debug, Clone, Error, Serialize, Deserialize, PartialEq, Eq)]
pub enum HostError {
    /// The requested primitive is not known to the host.
    #[error("unknown primitive: {0}")]
    UnknownPrimitive(String),

    /// Argument type mismatch.
    #[error("argument mismatch for primitive {primitive}: {detail}")]
    ArgumentMismatch {
        /// Primitive identifier.
        primitive: String,
        /// Diagnostic detail.
        detail: String,
    },

    /// Host rejected the call for policy reasons (sanctions, governance, ...).
    #[error("policy rejection: {0}")]
    PolicyRejection(String),

    /// Host failed for a transient reason.
    #[error("transient failure: {0}")]
    Transient(String),

    /// Host failed for a permanent reason.
    #[error("permanent failure: {0}")]
    Permanent(String),

    /// The host cannot discharge a safety predicate.
    #[error("safety predicate undischarged: {0:?}")]
    SafetyPredicateUndischarged(SafetyPredicate),
}

/// A primitive invocation as materialized by the evaluator.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimitiveCall {
    /// Primitive identifier.
    pub primitive: Primitive,
    /// Named arguments, already reduced to JSON values by the evaluator.
    pub args: BTreeMap<String, serde_json::Value>,
    /// Ambient jurisdiction at the call site.
    pub jurisdiction: String,
}

/// Outcome of a primitive call.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum HostOutcome {
    /// The primitive completed synchronously with a result value.
    Completed(serde_json::Value),
    /// The primitive suspended on a callback and will be resumed later.
    /// The evaluator treats this as an `Await<event, _>` value.
    Waiting {
        /// Callback event identifier.
        event: String,
        /// Opaque resume token.
        resume_token: String,
    },
}

/// Minimum host surface.
///
/// Implementations fulfill primitive calls, discharge safety predicates, and
/// answer jurisdictional resolution queries. Host implementations must be
/// deterministic when replayed: given the same inputs, the same outcome must
/// be produced.
pub trait OpHost: Send + Sync {
    /// Invoke a primitive. Returns either a completed value or a waiting
    /// callback.
    fn invoke(&self, call: &PrimitiveCall) -> Result<HostOutcome, HostError>;

    /// Canonicalize a jurisdiction identifier (e.g. `florida` →
    /// `us-florida`). Return the input unchanged when no alias is known.
    fn canonicalize_jurisdiction(&self, raw: &str) -> String {
        raw.to_string()
    }

    /// Discharge a compositional safety predicate against a context payload.
    /// Return `Ok(())` when the predicate is satisfied, `Err` otherwise.
    fn discharge_safety(
        &self,
        predicate: &SafetyPredicate,
        _context: &serde_json::Value,
    ) -> Result<(), HostError> {
        Err(HostError::SafetyPredicateUndischarged(predicate.clone()))
    }
}

/// A minimal no-op host used by tests and examples. Every primitive call is
/// reported as completed with a small record of what was invoked.
#[derive(Debug, Default, Clone)]
pub struct NoopHost;

impl OpHost for NoopHost {
    fn invoke(&self, call: &PrimitiveCall) -> Result<HostOutcome, HostError> {
        let mut obj = serde_json::Map::new();
        obj.insert(
            "primitive".to_string(),
            serde_json::Value::String(call.primitive.0.clone()),
        );
        obj.insert(
            "jurisdiction".to_string(),
            serde_json::Value::String(call.jurisdiction.clone()),
        );
        obj.insert(
            "args".to_string(),
            serde_json::Value::Object(
                call.args
                    .iter()
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect(),
            ),
        );
        Ok(HostOutcome::Completed(serde_json::Value::Object(obj)))
    }

    fn discharge_safety(
        &self,
        _predicate: &SafetyPredicate,
        _context: &serde_json::Value,
    ) -> Result<(), HostError> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn noop_host_echoes_call() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), serde_json::Value::from(1));
        let call = PrimitiveCall {
            primitive: Primitive("noop".to_string()),
            args,
            jurisdiction: "_default".to_string(),
        };
        let outcome = NoopHost.invoke(&call).unwrap();
        match outcome {
            HostOutcome::Completed(v) => assert!(v.is_object()),
            HostOutcome::Waiting { .. } => panic!("expected completed"),
        }
    }

    #[test]
    fn host_default_canonicalization_is_identity() {
        assert_eq!(NoopHost.canonicalize_jurisdiction("ae"), "ae");
    }
}
