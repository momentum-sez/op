//! Golden test — OECD Action 6 LOB tolling exception.
//!
//! The rule: treaty-benefits entitlement is granted (`Compliant`) unless
//! the beneficiary fails the limitation-on-benefits test. One exception
//! with priority 10 overrides the base. The compiled emission is a nested
//! `Match` on the guard's boolean result.
//!
//! Verdict table:
//!
//! | LOB failed | verdict |
//! |---|---|
//! | true | `NonCompliant { reason: "lob_failed" }` |
//! | false | `Compliant` |

use op_core::host::NoopHost;
use op_core::{OpExpr, Statement};
use op_lex_compiler::{
    compile_lex, run_program, CompileCtx, EvalResult, LexException, LexTerm, LexValue,
};

fn compliant() -> LexValue {
    LexValue::Variant {
        tag: "Compliant".to_string(),
        payload: Box::new(LexValue::Unit),
    }
}

fn non_compliant(reason: &str) -> LexValue {
    LexValue::Variant {
        tag: "NonCompliant".to_string(),
        payload: Box::new(LexValue::Record(vec![(
            "reason".to_string(),
            LexValue::Str(reason.to_string()),
        )])),
    }
}

fn build_rule(lob_failed: bool) -> LexTerm {
    LexTerm::Defeasible {
        name: "oecd.lob.tolling".to_string(),
        base: Box::new(LexTerm::Const(compliant())),
        exceptions: vec![LexException {
            guard: LexTerm::const_bool(lob_failed),
            body: LexTerm::Const(non_compliant("lob_failed")),
            priority: 10,
            source_position: 0,
        }],
    }
}

#[test]
fn compiled_shape_is_nested_match() {
    let term = build_rule(false);
    let ctx = CompileCtx::with_canonical_prelude("oecd.lob.tolling");
    let program = compile_lex(&term, &ctx).expect("admissible");

    match &program.body[0] {
        Statement::Return(OpExpr::Match { arms, .. }) => {
            assert_eq!(arms.len(), 2);
            let patterns: Vec<_> = arms.iter().map(|a| a.pattern.clone()).collect();
            assert_eq!(patterns, vec!["true", "false"]);
        }
        other => panic!("expected nested Match, got {other:?}"),
    }
}

#[test]
fn guard_false_yields_base_compliant() {
    let term = build_rule(false);
    let ctx = CompileCtx::with_canonical_prelude("oecd.lob.tolling");
    let program = compile_lex(&term, &ctx).unwrap();
    let host = NoopHost;
    match run_program(&program, &host) {
        EvalResult::Value(v) => assert_eq!(v["tag"], "Compliant"),
        EvalResult::Error(e) => panic!("eval error: {e}"),
    }
}

#[test]
fn guard_true_yields_exception_non_compliant() {
    let term = build_rule(true);
    let ctx = CompileCtx::with_canonical_prelude("oecd.lob.tolling");
    let program = compile_lex(&term, &ctx).unwrap();
    let host = NoopHost;
    match run_program(&program, &host) {
        EvalResult::Value(v) => {
            assert_eq!(v["tag"], "NonCompliant");
            assert_eq!(v["value"]["reason"], "lob_failed");
        }
        EvalResult::Error(e) => panic!("eval error: {e}"),
    }
}

#[test]
fn priority_order_respected_two_exceptions() {
    // Two exceptions: the higher-priority one (12) overrides the lower (8).
    // Both guards true — the higher-priority body must win.
    let term = LexTerm::Defeasible {
        name: "demo.priority".to_string(),
        base: Box::new(LexTerm::Const(compliant())),
        exceptions: vec![
            LexException {
                guard: LexTerm::const_bool(true),
                body: LexTerm::Const(non_compliant("lower_priority_body")),
                priority: 8,
                source_position: 0,
            },
            LexException {
                guard: LexTerm::const_bool(true),
                body: LexTerm::Const(non_compliant("higher_priority_body")),
                priority: 12,
                source_position: 1,
            },
        ],
    };

    let ctx = CompileCtx::with_canonical_prelude("demo.priority");
    let program = compile_lex(&term, &ctx).unwrap();
    let host = NoopHost;
    match run_program(&program, &host) {
        EvalResult::Value(v) => {
            assert_eq!(v["tag"], "NonCompliant");
            assert_eq!(v["value"]["reason"], "higher_priority_body");
        }
        EvalResult::Error(e) => panic!("eval error: {e}"),
    }
}
