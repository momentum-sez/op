use op_core::{host::NoopHost, ProgramPurposeTag};
use op_lex_compiler::{
    compile_lex, compile_lex_v1, run_program, AuthoredCompileCtxV1, CompileCtx, CompileError,
    EvalResult, LexException, LexTerm,
};

#[test]
fn lex_lowering_retains_exact_purpose_through_compilation_and_reference_execution() {
    let term = LexTerm::Defeasible {
        name: "unrelated.rule_name".to_string(),
        base: Box::new(LexTerm::const_int(3)),
        exceptions: vec![LexException {
            guard: LexTerm::const_bool(true),
            body: LexTerm::const_int(7),
            priority: 10,
            source_position: 0,
        }],
    };
    let context = CompileCtx::with_canonical_prelude("different.program_name");
    let historical = compile_lex(&term, &context).unwrap();
    let context = AuthoredCompileCtxV1::new(
        ProgramPurposeTag::new("Entity.Onboarding_v2").unwrap(),
        context,
    );
    let authored = compile_lex_v1(&term, &context).unwrap();
    assert_eq!(authored.purpose().as_str(), "Entity.Onboarding_v2");
    assert_eq!(authored.program(), &historical);
    assert_eq!(
        run_program(authored.program(), &NoopHost),
        EvalResult::Value(serde_json::json!(7))
    );
    assert_eq!(
        serde_json::to_value(&authored).unwrap()["purpose"],
        "Entity.Onboarding_v2"
    );
}

#[test]
fn authored_lex_entry_point_still_rejects_invalid_terms_and_output_structure() {
    let context = AuthoredCompileCtxV1::new(
        ProgramPurposeTag::new("Entity.Onboarding_v2").unwrap(),
        CompileCtx::with_canonical_prelude("example.program"),
    );
    assert!(matches!(
        compile_lex_v1(&LexTerm::var("missing_variable", 0), &context),
        Err(CompileError::UnboundVariable { .. })
    ));

    let empty_name = AuthoredCompileCtxV1::new(
        ProgramPurposeTag::new("Entity.Onboarding_v2").unwrap(),
        CompileCtx::with_canonical_prelude(""),
    );
    match compile_lex_v1(&LexTerm::const_bool(true), &empty_name) {
        Err(CompileError::EmittedOpTypecheckFailed { errors }) => {
            assert!(errors
                .iter()
                .any(|error| error.contains("program name cannot be empty")));
        }
        other => panic!("expected invalid output structure, got {other:?}"),
    }
}
