//! Golden test — sanctions-dominance rule.
//!
//! The rule: if the principal appears on any sanctions list, the verdict is
//! `SanctionsBlocked`; otherwise the verdict is `Compliant`. Compiles into
//! `OpExpr::Call("sanctions.check", { principal })`; the sanctions-bottom
//! semantics is discharged by the host during execution.

use op_core::host::NoopHost;
use op_core::{
    HostError, HostOutcome, OpExpr, OpHost, Primitive, PrimitiveCall, SafetyPredicate, Statement,
};
use op_lex_compiler::{compile_lex, run_program, CompileCtx, EvalResult, LexTerm};
use serde_json::{json, Value};

/// A host implementation that keeps an in-memory sanctions list and
/// produces the `Compliant` / `SanctionsBlocked` verdict in response to
/// `sanctions.check` invocations.
#[derive(Debug, Clone)]
struct SanctionsHost {
    sanctioned_principals: Vec<String>,
}

impl SanctionsHost {
    fn with(list: &[&str]) -> Self {
        Self {
            sanctioned_principals: list.iter().map(|s| s.to_string()).collect(),
        }
    }
}

impl OpHost for SanctionsHost {
    fn invoke(&self, call: &PrimitiveCall) -> Result<HostOutcome, HostError> {
        if call.primitive == Primitive("sanctions.check".to_string()) {
            let principal = call
                .args
                .get("principal")
                .and_then(Value::as_str)
                .ok_or_else(|| HostError::ArgumentMismatch {
                    primitive: "sanctions.check".to_string(),
                    detail: "missing principal string".to_string(),
                })?;
            let blocked = self
                .sanctioned_principals
                .iter()
                .any(|p| p == principal);
            let verdict = if blocked {
                json!({ "tag": "SanctionsBlocked", "value": { "principal": principal } })
            } else {
                json!({ "tag": "Compliant", "value": null })
            };
            return Ok(HostOutcome::Completed(verdict));
        }
        Err(HostError::UnknownPrimitive(call.primitive.0.clone()))
    }

    fn discharge_safety(
        &self,
        _pred: &SafetyPredicate,
        _ctx: &Value,
    ) -> Result<(), HostError> {
        Ok(())
    }
}

#[test]
fn compiled_shape_is_sanctions_call() {
    let term = LexTerm::sanctions_dominance_of(LexTerm::const_string("entity-A"));
    let ctx = CompileCtx::with_canonical_prelude("demo.sanctions");
    let program = compile_lex(&term, &ctx).unwrap();
    match &program.body[0] {
        Statement::Return(OpExpr::Call(name, args)) => {
            assert_eq!(name, "sanctions.check");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0].0, "principal");
        }
        other => panic!("expected sanctions call, got {other:?}"),
    }
}

#[test]
fn sanctioned_principal_yields_sanctions_blocked() {
    let term = LexTerm::sanctions_dominance_of(LexTerm::const_string("entity-sdn-1"));
    let ctx = CompileCtx::with_canonical_prelude("demo.sanctions");
    let program = compile_lex(&term, &ctx).unwrap();
    let host = SanctionsHost::with(&["entity-sdn-1"]);
    match run_program(&program, &host) {
        EvalResult::Value(v) => {
            assert_eq!(v["tag"], "SanctionsBlocked");
            assert_eq!(v["value"]["principal"], "entity-sdn-1");
        }
        EvalResult::Error(e) => panic!("eval error: {e}"),
    }
}

#[test]
fn clean_principal_yields_compliant() {
    let term = LexTerm::sanctions_dominance_of(LexTerm::const_string("entity-clean"));
    let ctx = CompileCtx::with_canonical_prelude("demo.sanctions");
    let program = compile_lex(&term, &ctx).unwrap();
    let host = SanctionsHost::with(&["entity-sdn-1"]);
    match run_program(&program, &host) {
        EvalResult::Value(v) => {
            assert_eq!(v["tag"], "Compliant");
        }
        EvalResult::Error(e) => panic!("eval error: {e}"),
    }
}

#[test]
fn noop_host_returns_echo_record() {
    // Cross-check: the noop host always returns a generic echo — the
    // sanctions-dominance scrutinee does not realize the verdict shape unless
    // the host implements `sanctions.check`.
    let term = LexTerm::sanctions_dominance_of(LexTerm::const_string("x"));
    let ctx = CompileCtx::with_canonical_prelude("demo.sanctions");
    let program = compile_lex(&term, &ctx).unwrap();
    let host = NoopHost;
    match run_program(&program, &host) {
        EvalResult::Value(v) => {
            // NoopHost echoes the call back as a record.
            assert_eq!(v["primitive"], "sanctions.check");
        }
        EvalResult::Error(e) => panic!("eval error: {e}"),
    }
}

#[test]
fn program_declares_sanctions_check_effect() {
    let term = LexTerm::sanctions_dominance_of(LexTerm::const_string("any"));
    let ctx = CompileCtx::with_canonical_prelude("demo.sanctions");
    let program = compile_lex(&term, &ctx).unwrap();
    assert!(program
        .effects
        .contains(&op_core::Effect::SanctionsCheck));
}
