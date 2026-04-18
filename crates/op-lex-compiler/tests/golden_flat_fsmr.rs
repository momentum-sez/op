//! Golden test — Seychelles IBC first-shareholder-meeting requirement.
//!
//! The rule: a Seychelles IBC must hold its first shareholder meeting no
//! later than 18 months after incorporation. There are no statutory
//! exceptions in the flat form — the rule is a `Defeasible` with an empty
//! exception list, compiling to `choose { else -> [[base]] }`, which at the
//! expression level reduces to the compiled base.
//!
//! End-to-end check: compile the admissible Lex term, inspect the emitted
//! `OpProgram` for the flat-rule shape, execute it under a no-op host, and
//! assert the verdict matches the base.

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

#[test]
fn flat_rule_compiles_to_base_expression() {
    // The rule body is the constant verdict `Compliant` — simplest flat
    // evaluation: the base holds unconditionally with no exception guards.
    let term = LexTerm::Defeasible {
        name: "seychelles.fsmr".to_string(),
        base: Box::new(LexTerm::Const(compliant())),
        exceptions: vec![],
    };

    let ctx = CompileCtx::with_canonical_prelude("seychelles.fsmr");
    let program = compile_lex(&term, &ctx).expect("flat rule must compile");

    // Emission shape: with zero exceptions, the folded accumulator is the
    // compiled base directly, not a nested match.
    match &program.body[0] {
        Statement::Return(OpExpr::Record(fields)) => {
            let names: Vec<_> = fields.iter().map(|(k, _)| k.clone()).collect();
            assert_eq!(names, vec!["tag", "value"]);
        }
        other => panic!("expected Return(Record) for flat rule, got {other:?}"),
    }
}

#[test]
fn flat_rule_executes_to_compliant() {
    let term = LexTerm::Defeasible {
        name: "seychelles.fsmr".to_string(),
        base: Box::new(LexTerm::Const(compliant())),
        exceptions: vec![],
    };

    let ctx = CompileCtx::with_canonical_prelude("seychelles.fsmr");
    let program = compile_lex(&term, &ctx).unwrap();

    let host = NoopHost;
    let result = run_program(&program, &host);
    match result {
        EvalResult::Value(v) => {
            assert_eq!(v["tag"], "Compliant");
        }
        EvalResult::Error(e) => panic!("unexpected eval error: {e}"),
    }
}

#[test]
fn flat_rule_non_compliant_base_propagates() {
    let non_compliant = LexValue::Variant {
        tag: "NonCompliant".to_string(),
        payload: Box::new(LexValue::Record(vec![(
            "reason".to_string(),
            LexValue::Str("fsmr_overdue".to_string()),
        )])),
    };
    let term = LexTerm::Defeasible {
        name: "seychelles.fsmr".to_string(),
        base: Box::new(LexTerm::Const(non_compliant)),
        exceptions: vec![],
    };

    let ctx = CompileCtx::with_canonical_prelude("seychelles.fsmr");
    let program = compile_lex(&term, &ctx).unwrap();

    let host = NoopHost;
    match run_program(&program, &host) {
        EvalResult::Value(v) => {
            assert_eq!(v["tag"], "NonCompliant");
            assert_eq!(v["value"]["reason"], "fsmr_overdue");
        }
        EvalResult::Error(e) => panic!("unexpected eval error: {e}"),
    }
}

#[test]
fn flat_rule_with_empty_exceptions_has_no_nested_match() {
    let term = LexTerm::Defeasible {
        name: "seychelles.fsmr".to_string(),
        base: Box::new(LexTerm::Const(compliant())),
        exceptions: vec![],
    };

    let ctx = CompileCtx::with_canonical_prelude("seychelles.fsmr");
    let program = compile_lex(&term, &ctx).unwrap();

    match &program.body[0] {
        Statement::Return(OpExpr::Match { .. }) => {
            panic!("flat rule must not introduce a nested Match");
        }
        _ => {}
    }
}

// Using `LexException` so the import sees a use; the tests above don't need
// it, but this keeps the test file self-describing about the shape the
// compiler accepts.
fn _touch_exception() -> LexException {
    LexException {
        guard: LexTerm::const_bool(true),
        body: LexTerm::const_bool(false),
        priority: 0,
        source_position: 0,
    }
}
