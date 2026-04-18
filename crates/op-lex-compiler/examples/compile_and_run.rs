//! End-to-end example: compile a Seychelles first-shareholder-meeting Lex
//! rule with a tolling exception, print the emitted Op program, and execute
//! it under a minimal host.
//!
//! Run with:
//!
//! ```bash
//! cargo run --example compile_and_run -p op-lex-compiler
//! ```

use op_core::{OpProgram, Statement};
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

fn build_rule(tolling_invoked: bool) -> LexTerm {
    // The rule: first shareholder meeting must be held within 18 months of
    // incorporation. One tolling exception: if the entity is in a
    // court-ordered wind-down, the requirement is suspended for the duration.
    LexTerm::Defeasible {
        name: "seychelles.fsmr".to_string(),
        base: Box::new(LexTerm::Const(non_compliant("fsmr_overdue"))),
        exceptions: vec![LexException {
            guard: LexTerm::const_bool(tolling_invoked),
            body: LexTerm::Const(compliant()),
            priority: 10,
            source_position: 0,
        }],
    }
}

fn print_program(program: &OpProgram) {
    println!("== Op program =======================");
    println!("name:         {}", program.name);
    println!("jurisdiction: {}", program.jurisdiction);
    println!("version:      {}", program.metadata.version);
    println!("description:  {}", program.metadata.description);
    println!("inputs:       {:?}", program.inputs);
    println!("outputs:      {:?}", program.outputs);
    println!("effects:      {:?}", program.effects);
    println!("body:");
    for (i, stmt) in program.body.iter().enumerate() {
        match stmt {
            Statement::Return(expr) => println!("  [{i}] return {}", short_expr(expr)),
            other => println!("  [{i}] {other:?}"),
        }
    }
}

fn short_expr(expr: &op_core::OpExpr) -> String {
    let s = format!("{expr:?}");
    if s.len() > 600 {
        format!("{}…", &s[..600])
    } else {
        s
    }
}

fn main() {
    println!("== Lex term =========================");
    let term = build_rule(false);
    println!("{:#?}", &term);
    println!();

    let ctx = CompileCtx::with_canonical_prelude("seychelles.fsmr.example");
    let program = compile_lex(&term, &ctx).expect("admissible rule must compile");
    print_program(&program);
    println!();

    println!("== Execution: tolling not invoked ===");
    let host = op_core::host::NoopHost;
    let untolled = build_rule(false);
    let untolled_prog = compile_lex(&untolled, &ctx).unwrap();
    let untolled_result = run_program(&untolled_prog, &host);
    println!("result: {untolled_result:?}");
    println!();

    println!("== Execution: tolling invoked =======");
    let tolled = build_rule(true);
    let tolled_prog = compile_lex(&tolled, &ctx).unwrap();
    let tolled_result = run_program(&tolled_prog, &host);
    println!("result: {tolled_result:?}");
    println!();

    println!("== Sanctions-dominance example ======");
    let sanctions_term = LexTerm::sanctions_dominance_of(LexTerm::const_string("principal-X"));
    let sanctions_prog =
        compile_lex(&sanctions_term, &CompileCtx::with_canonical_prelude("demo.sanctions"))
            .unwrap();
    print_program(&sanctions_prog);
    match run_program(&sanctions_prog, &host) {
        EvalResult::Value(v) => println!("execution value: {v}"),
        EvalResult::Error(e) => println!("execution error: {e}"),
    }

    println!();
    println!("== Summary ==========================");
    println!("All cases demonstrated: Const, Var (prelude), Match (inside Defeasible),");
    println!("Defeasible (tolling), SanctionsDominance, HoleFill.");
}
