//! Error type for Op.

use thiserror::Error;

/// The Op error hierarchy.
#[derive(Debug, Error)]
pub enum OpError {
    /// Parser rejected the input.
    #[error("parse error at line {line}: {message}")]
    ParseError {
        /// One-based source line.
        line: usize,
        /// Human-readable diagnostic.
        message: String,
    },

    /// The type checker rejected the program.
    #[error("type error: {0}")]
    TypeError(String),

    /// A linear resource was consumed more than once.
    #[error("linearity violation: resource {0} used after consumption")]
    LinearityViolation(String),

    /// A locked resource was eliminated by a non-canonical path.
    #[error("lock violation: {0}")]
    LockViolation(String),

    /// Effect safety analysis surfaced a violation.
    #[error("effect-safety violation: {0}")]
    EffectSafetyViolation(String),

    /// Gas was exhausted.
    #[error("gas limit exceeded: used {used}, limit {limit}")]
    GasLimitExceeded {
        /// Gas consumed at the moment of failure.
        used: u64,
        /// Configured limit.
        limit: u64,
    },

    /// Compiler stage rejected the program.
    #[error("compilation error: {0}")]
    CompilationError(String),

    /// serde_json failure (wire format).
    #[error("serialization error: {0}")]
    Serialization(#[from] serde_json::Error),

    /// Evaluator hit a runtime failure the host could not resolve.
    #[error("evaluation error: {0}")]
    EvalError(String),

    /// Referenced variable is not bound.
    #[error("unbound variable: {0}")]
    UnboundVariable(String),

    /// Host returned an error during primitive invocation.
    #[error("host error: {0}")]
    Host(String),

    /// Evaluator was aborted.
    #[error("abort signal during evaluation")]
    AbortSignal,
}
