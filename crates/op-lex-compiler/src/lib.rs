//! # op-lex-compiler — the compilation function `[[·]] : Lex -> Op`
//!
//! Realizes the §6.2 compilation function from the Op paper as a running
//! reference implementation. The compiler is total on the admissible
//! fragment of Lex and rejects non-admissible inputs with a structured
//! error pointing at the violated clause.
//!
//! ## Entry point
//!
//! ```ignore
//! use op_lex_compiler::{compile_lex, CompileCtx, LexTerm};
//!
//! let term = LexTerm::const_bool(true);
//! let ctx = CompileCtx::with_canonical_prelude("demo.trivial");
//! let program = compile_lex(&term, &ctx).expect("admissible constant");
//! ```
//!
//! ## Admissibility
//!
//! The admissibility predicate `A(·)` decides membership in the compilation
//! domain before any compilation case fires. See
//! [`admissibility::check_admissible`]. A non-admissible input produces a
//! [`CompileError::NotAdmissible`] value whose `reason` field identifies the
//! specific clause that rejected the term.
//!
//! ## Compilation cases
//!
//! Six cases cover the admissible fragment:
//!
//! 1. [`case_const`] — constant lifting.
//! 2. [`case_var`] — prelude-scoped variable resolution.
//! 3. [`case_match`] — pattern match to Op `Match` with a materialized
//!    fail-closed catch-all.
//! 4. [`case_defeasible`] — defeasible rule to nested guard `Match`, with
//!    exceptions ordered by (priority DESC, source-position ASC).
//! 5. [`case_sanctions`] — sanctions-dominance to the host's
//!    `sanctions.check` primitive, carrying the sanctions-bottom semantics
//!    described in Op §3.9.
//! 6. [`case_fill`] — filled discretion hole to an attestation-append paired
//!    with the lifted value, under the τ-labelled (silent) bisimulation
//!    case of Op §6.3.

#![warn(missing_docs)]

pub mod admissibility;
pub mod ast;
pub mod case_const;
pub mod case_defeasible;
pub mod case_fill;
pub mod case_match;
pub mod case_sanctions;
pub mod case_var;
pub mod context;
pub mod error;
pub mod interp;
pub mod lift;

pub use interp::{run_program, EvalResult};

pub use ast::{LexBranch, LexException, LexLoc, LexTerm, LexValue, Witness};
pub use context::{CompileCtx, Jurisdiction, PreludeBinding, PreludeCallable, PreludeLower};
pub use error::{AdmissibilityViolation, CompileError};

use op_core::{
    ApprovalMode, BinOp, Contracts, Effect, MatchArm, OpExpr, OpProgram, OpType, ProgramMetadata,
    Statement, UnOp,
};

/// Compile an admissible Lex term into an Op program.
///
/// # Errors
///
/// - [`CompileError::NotAdmissible`] when the term fails one of the
///   admissibility clauses.
/// - [`CompileError::UnsupportedPreludeCall`] when a call names a callee not
///   registered in the prelude.
/// - [`CompileError::UnboundVariable`] when a variable reference is outside
///   the prelude value set.
/// - [`CompileError::UnfilledHole`] when a hole with no filler surfaces.
/// - [`CompileError::ModalUnsupported`] / [`CompileError::TemporalCoercion`]
///   — discharged by construction in the admissibility gate; surface as
///   defence-in-depth.
/// - [`CompileError::PatternExhaustivenessUndecidable`] when a match's
///   exhaustiveness cannot be decided under the prelude.
pub fn compile_lex(term: &LexTerm, ctx: &CompileCtx) -> Result<OpProgram, CompileError> {
    admissibility::check_admissible(term, &ctx.prelude)?;
    let body_expr = compile_expr(term, ctx)?;
    Ok(build_program(body_expr, ctx))
}

/// Core expression-level compilation. Dispatches to the six case modules.
pub(crate) fn compile_expr(term: &LexTerm, ctx: &CompileCtx) -> Result<OpExpr, CompileError> {
    match term {
        LexTerm::Const(v) => Ok(case_const::compile_const(v)),

        LexTerm::Var { name, .. } => case_var::compile_var(name, ctx),

        LexTerm::Match {
            scrutinee,
            branches,
        } => {
            let compiled_scrutinee = compile_expr(scrutinee, ctx)?;
            let mut compile_one = |t: &LexTerm, c: &CompileCtx| compile_expr(t, c);
            case_match::compile_match(compiled_scrutinee, branches, &mut compile_one, ctx)
        }

        LexTerm::Defeasible {
            base, exceptions, ..
        } => {
            let mut compile_one = |t: &LexTerm, c: &CompileCtx| compile_expr(t, c);
            case_defeasible::compile_defeasible(base, exceptions, &mut compile_one, ctx)
        }

        LexTerm::SanctionsDominance { principal } => {
            let compiled_principal = compile_expr(principal, ctx)?;
            Ok(case_sanctions::compile_sanctions(compiled_principal, ctx))
        }

        LexTerm::HoleFill {
            hole_id,
            value,
            witness,
        } => {
            let compiled_value = compile_expr(value, ctx)?;
            Ok(case_fill::compile_fill(hole_id, compiled_value, witness))
        }

        LexTerm::PreludeCall { callee, args } => compile_prelude_call(callee, args, ctx),
    }
}

/// Lower a prelude call into an Op expression per the callable's lowering
/// strategy. Registered on the prelude binding.
fn compile_prelude_call(
    callee: &str,
    args: &[LexTerm],
    ctx: &CompileCtx,
) -> Result<OpExpr, CompileError> {
    let callable =
        ctx.prelude
            .lookup_callable(callee)
            .ok_or_else(|| CompileError::UnsupportedPreludeCall {
                name: callee.to_string(),
            })?;

    let compiled_args: Vec<OpExpr> = args
        .iter()
        .map(|a| compile_expr(a, ctx))
        .collect::<Result<Vec<_>, _>>()?;

    match &callable.lower {
        PreludeLower::BinOp(op) => match compiled_args.as_slice() {
            [a, b] => Ok(OpExpr::BinOp(*op, Box::new(a.clone()), Box::new(b.clone()))),
            _ => Err(CompileError::UnsupportedPreludeCall {
                name: format!("{callee}: BinOp expects exactly 2 args"),
            }),
        },
        PreludeLower::UnOp(op) => match compiled_args.as_slice() {
            [a] => Ok(OpExpr::UnOp(*op, Box::new(a.clone()))),
            _ => Err(CompileError::UnsupportedPreludeCall {
                name: format!("{callee}: UnOp expects exactly 1 arg"),
            }),
        },
        PreludeLower::PrimitiveCall { name } => {
            let named = args
                .iter()
                .enumerate()
                .zip(compiled_args.iter())
                .map(|((i, _), e)| (format!("arg{i}"), e.clone()))
                .collect();
            Ok(OpExpr::Call(name.clone(), named))
        }
        PreludeLower::ConstantLiteral(expr) | PreludeLower::FixedExpr(expr) => Ok(expr.clone()),
    }
}

/// Wrap a compiled expression into a full `OpProgram` whose body returns it.
///
/// The emitted program advertises a single output field `result` whose type
/// is inferred from the compiled body. A hardcoded `verdict: Verdict`
/// advertisement would over-specify the output type for bodies that lower
/// into a non-variant expression (e.g. a raw boolean or integer constant);
/// the type inferred at compile time is always correct by construction.
fn build_program(body: OpExpr, ctx: &CompileCtx) -> OpProgram {
    let inferred_output = infer_expr_type(&body, ctx);
    OpProgram {
        name: ctx.program_name.clone(),
        jurisdiction: ctx.jurisdiction.0.clone(),
        metadata: ProgramMetadata {
            version: "0.1.0".to_string(),
            description: "Compiled from Lex via [[.]] : Lex -> Op.".to_string(),
        },
        inputs: vec![],
        outputs: vec![("result".to_string(), inferred_output)],
        effects: program_effects(&body),
        participants: vec![],
        approval: Option::<ApprovalMode>::None,
        contracts: Contracts::default(),
        body: vec![Statement::Return(body)],
        gas_budget: ctx.gas_budget.clone(),
    }
}

fn verdict_variant() -> Vec<(String, OpType)> {
    vec![
        ("Compliant".to_string(), OpType::Unit),
        (
            "NonCompliant".to_string(),
            OpType::Record(vec![("reason".to_string(), OpType::String)]),
        ),
        ("SanctionsBlocked".to_string(), OpType::Unit),
    ]
}

/// Infer the Op type of a compiled expression.
///
/// The compiled fragment is limited to the shapes the six §6.2 cases emit
/// — literals, records, calls, BinOp/UnOp, Match, Seq. The type is
/// reconstructed by structural recursion with conservative fallbacks for
/// host-dependent calls.
pub(crate) fn infer_expr_type(expr: &OpExpr, ctx: &CompileCtx) -> OpType {
    match expr {
        OpExpr::Unit => OpType::Unit,
        OpExpr::Bool(_) => OpType::Bool,
        OpExpr::Int(_) => OpType::Int,
        OpExpr::String(_) => OpType::String,
        OpExpr::Null => OpType::Option(Box::new(OpType::Unit)),
        OpExpr::Record(fields) => {
            let inferred: Vec<(String, OpType)> = fields
                .iter()
                .map(|(name, e)| (name.clone(), infer_expr_type(e, ctx)))
                .collect();
            OpType::Record(inferred)
        }
        OpExpr::List(items) => {
            let inner = items
                .first()
                .map(|e| infer_expr_type(e, ctx))
                .unwrap_or(OpType::Unit);
            OpType::List(Box::new(inner))
        }
        OpExpr::Tuple(items) => {
            OpType::Tuple(items.iter().map(|e| infer_expr_type(e, ctx)).collect())
        }
        OpExpr::Var(name) => ctx
            .lookup_binder(name)
            .cloned()
            .or_else(|| ctx.prelude.lookup_value(name).map(|(ty, _)| ty.clone()))
            .unwrap_or(OpType::Record(vec![])),
        OpExpr::Call(name, _args) => {
            // A named callable surfaces the callable's declared return type
            // via the canonical-prelude registration.
            if let Some(callable) = ctx.prelude.lookup_callable(name) {
                return callable.ty.clone();
            }
            match name.as_str() {
                "sanctions.check" => OpType::Variant(verdict_variant()),
                "attestation.append" => OpType::Record(vec![]),
                _ => OpType::Record(vec![]),
            }
        }
        OpExpr::BinOp(op, _a, _b) => match op {
            op_core::BinOp::Eq
            | op_core::BinOp::Ne
            | op_core::BinOp::Lt
            | op_core::BinOp::Le
            | op_core::BinOp::Gt
            | op_core::BinOp::Ge
            | op_core::BinOp::And
            | op_core::BinOp::Or
            | op_core::BinOp::In
            | op_core::BinOp::Contains => OpType::Bool,
            op_core::BinOp::Add | op_core::BinOp::Sub | op_core::BinOp::Mul => OpType::Int,
        },
        OpExpr::UnOp(op, a) => match op {
            op_core::UnOp::Not => OpType::Bool,
            op_core::UnOp::Neg => infer_expr_type(a, ctx),
        },
        OpExpr::Coalesce(a, _b) => infer_expr_type(a, ctx),
        // Seq's type is the type of its second operand (F6 § canonical Seq).
        OpExpr::Seq(_a, b) => infer_expr_type(b, ctx),
        OpExpr::Field(_, _) => OpType::Record(vec![]),
        OpExpr::Match { arms, catch_all, .. } => {
            // Conservative: return the type of the first arm's body, falling
            // back to the catch-all. All arms + catch-all should share a
            // type by admissibility of the source Lex match.
            arms.first()
                .map(|arm| infer_expr_type(&arm.body, ctx))
                .unwrap_or_else(|| infer_expr_type(catch_all, ctx))
        }
        OpExpr::Await { event, .. } => OpType::Await {
            event: event.clone(),
            payload: Box::new(OpType::Record(vec![])),
        },
        OpExpr::AssertSafety(_) => OpType::Unit,
        OpExpr::ConsumeLinear(inner) => infer_expr_type(inner, ctx),
        OpExpr::Lock { resource, .. } => {
            OpType::Locked(Box::new(infer_expr_type(resource, ctx)))
        }
        OpExpr::CommitTransfer { locked, .. } => infer_expr_type(locked, ctx),
        OpExpr::ReleaseLock { locked, .. } => infer_expr_type(locked, ctx),
    }
}

/// Infer the program-level effect row from the body. Conservative: emits
/// every effect mentioned in any call inside the body.
fn program_effects(body: &OpExpr) -> Vec<Effect> {
    let mut effects = std::collections::BTreeSet::new();
    effects.insert(Effect::Pure);
    walk_effects(body, &mut effects);
    let mut vec: Vec<Effect> = effects.into_iter().collect();
    vec.sort();
    vec
}

fn walk_effects(expr: &OpExpr, acc: &mut std::collections::BTreeSet<Effect>) {
    match expr {
        OpExpr::Call(name, args) => {
            match name.as_str() {
                "sanctions.check" => {
                    acc.insert(Effect::SanctionsCheck);
                }
                "attestation.append" => {
                    acc.insert(Effect::ProofEmit);
                }
                _ => {}
            }
            for (_, a) in args {
                walk_effects(a, acc);
            }
        }
        OpExpr::BinOp(_, a, b) => {
            walk_effects(a, acc);
            walk_effects(b, acc);
        }
        OpExpr::UnOp(_, a) => walk_effects(a, acc),
        OpExpr::Record(fields) => {
            for (_, e) in fields {
                walk_effects(e, acc);
            }
        }
        OpExpr::List(es) | OpExpr::Tuple(es) => {
            for e in es {
                walk_effects(e, acc);
            }
        }
        OpExpr::Match {
            scrutinee,
            arms,
            catch_all,
        } => {
            walk_effects(scrutinee, acc);
            for a in arms {
                walk_effects(&a.body, acc);
            }
            walk_effects(catch_all, acc);
        }
        OpExpr::Coalesce(a, b) | OpExpr::Seq(a, b) => {
            walk_effects(a, acc);
            walk_effects(b, acc);
        }
        OpExpr::Field(e, _) => walk_effects(e, acc),
        _ => {}
    }
}

// Re-export `BinOp` / `UnOp` / `MatchArm` for tests / examples that
// introspect the emitted AST.
pub use op_core::{BinOp as OpBinOp, MatchArm as OpMatchArm, UnOp as OpUnOp};

// Silence unused-import lint when no test references these.
#[allow(dead_code)]
fn _touch_reexports() -> (BinOp, UnOp, MatchArm) {
    (
        BinOp::Eq,
        UnOp::Not,
        MatchArm {
            pattern: "_".to_string(),
            binding: "_".to_string(),
            body: OpExpr::Unit,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn const_bool_compiles_to_literal() {
        let ctx = CompileCtx::with_canonical_prelude("demo");
        let program = compile_lex(&LexTerm::const_bool(true), &ctx).unwrap();
        match &program.body[0] {
            Statement::Return(OpExpr::Bool(true)) => {}
            other => panic!("expected Return(Bool(true)), got {other:?}"),
        }
    }

    #[test]
    fn const_int_compiles_to_literal() {
        let ctx = CompileCtx::with_canonical_prelude("demo");
        let program = compile_lex(&LexTerm::const_int(42), &ctx).unwrap();
        match &program.body[0] {
            Statement::Return(OpExpr::Int(42)) => {}
            other => panic!("expected Return(Int(42)), got {other:?}"),
        }
    }

    #[test]
    fn var_unbound_rejected() {
        let ctx = CompileCtx::with_canonical_prelude("demo");
        let result = compile_lex(&LexTerm::var("nonexistent", 0), &ctx);
        assert!(matches!(result, Err(CompileError::UnboundVariable { .. })));
    }

    #[test]
    fn var_bound_to_prelude_true() {
        let ctx = CompileCtx::with_canonical_prelude("demo");
        let program = compile_lex(&LexTerm::var("prelude.true", 0), &ctx).unwrap();
        match &program.body[0] {
            Statement::Return(OpExpr::Bool(true)) => {}
            other => panic!("expected Return(Bool(true)), got {other:?}"),
        }
    }

    #[test]
    fn sanctions_dominance_emits_call() {
        let ctx = CompileCtx::with_canonical_prelude("demo.sanctions");
        let term =
            LexTerm::sanctions_dominance_of(LexTerm::const_string("entity-0xDEADBEEF"));
        let program = compile_lex(&term, &ctx).unwrap();
        match &program.body[0] {
            Statement::Return(OpExpr::Call(name, args)) => {
                assert_eq!(name, "sanctions.check");
                assert_eq!(args.len(), 1);
                assert_eq!(args[0].0, "principal");
                assert!(program.effects.contains(&Effect::SanctionsCheck));
            }
            other => panic!("expected sanctions call, got {other:?}"),
        }
    }

    #[test]
    fn hole_fill_emits_seq_preserving_value_type() {
        // §6.2: [[fill(h, v, w)]] = [[v]] with τ-labelled attestation append.
        // The emitted shape must be OpExpr::Seq(attestation_call, value).
        // The sequenced value preserves the Op-type of the lifted value so
        // the §6.3 weak bisimulation holds.
        let ctx = CompileCtx::with_canonical_prelude("demo.fill");
        let term = LexTerm::HoleFill {
            hole_id: "h1".to_string(),
            value: Box::new(LexTerm::const_int(5)),
            witness: Witness {
                authority: "ofac".to_string(),
                digest: "0xabc".to_string(),
                timestamp: "2026-04-18T10:00:00Z".to_string(),
            },
        };
        let program = compile_lex(&term, &ctx).unwrap();
        match &program.body[0] {
            Statement::Return(OpExpr::Seq(attestation, value)) => {
                // The attestation sub-expression is a call into `attestation.append`.
                match attestation.as_ref() {
                    OpExpr::Call(name, args) => {
                        assert_eq!(name, "attestation.append");
                        let keys: Vec<_> = args.iter().map(|(k, _)| k.as_str()).collect();
                        assert!(keys.contains(&"hole_id"));
                        assert!(keys.contains(&"authority"));
                        assert!(keys.contains(&"digest"));
                        assert!(keys.contains(&"timestamp"));
                    }
                    other => panic!("expected attestation.append call, got {other:?}"),
                }
                // The value sub-expression is exactly `[[5]] = OpExpr::Int(5)`.
                match value.as_ref() {
                    OpExpr::Int(5) => {}
                    other => panic!("expected Int(5) as sequenced value, got {other:?}"),
                }
                // Effect row carries ProofEmit via the attestation call.
                assert!(program.effects.contains(&Effect::ProofEmit));
            }
            other => panic!("expected Seq(attestation, value), got {other:?}"),
        }
    }

    #[test]
    fn outputs_reflect_inferred_body_type_for_bool_const() {
        let ctx = CompileCtx::with_canonical_prelude("demo");
        let program = compile_lex(&LexTerm::const_bool(true), &ctx).unwrap();
        // F5: outputs carry `result: T` where T is inferred from the body,
        // not a hardcoded Verdict variant.
        assert_eq!(program.outputs.len(), 1);
        assert_eq!(program.outputs[0].0, "result");
        assert_eq!(program.outputs[0].1, OpType::Bool);
    }

    #[test]
    fn outputs_reflect_inferred_body_type_for_int_const() {
        let ctx = CompileCtx::with_canonical_prelude("demo");
        let program = compile_lex(&LexTerm::const_int(42), &ctx).unwrap();
        assert_eq!(program.outputs[0].0, "result");
        assert_eq!(program.outputs[0].1, OpType::Int);
    }

    #[test]
    fn outputs_reflect_variant_type_for_sanctions_body() {
        let ctx = CompileCtx::with_canonical_prelude("demo.sanctions");
        let term = LexTerm::sanctions_dominance_of(LexTerm::const_string("entity-0"));
        let program = compile_lex(&term, &ctx).unwrap();
        // The sanctions.check callable is registered with a variant return.
        match &program.outputs[0].1 {
            OpType::Variant(ctors) => {
                let names: Vec<_> = ctors.iter().map(|(n, _)| n.as_str()).collect();
                assert!(names.contains(&"Compliant"));
                assert!(names.contains(&"SanctionsBlocked"));
            }
            other => panic!("expected Variant output, got {other:?}"),
        }
    }

    #[test]
    fn seq_preserves_value_type_under_attestation_failure() {
        // F6: attestation.append in a Seq position must not abort the Seq
        // when the host errors on that call. The value operand carries the
        // result. This is the §6.3 τ-labelled bisimulation case.
        use op_core::host::{HostError, HostOutcome, OpHost, PrimitiveCall};
        struct FailingProofHost;
        impl OpHost for FailingProofHost {
            fn invoke(
                &self,
                call: &PrimitiveCall,
            ) -> Result<HostOutcome, HostError> {
                if call.primitive.0 == "attestation.append" {
                    return Err(HostError::Transient(
                        "proof bundle writer offline".to_string(),
                    ));
                }
                Ok(HostOutcome::Completed(serde_json::Value::Null))
            }
        }
        let ctx = CompileCtx::with_canonical_prelude("demo.fill");
        let term = LexTerm::HoleFill {
            hole_id: "h1".to_string(),
            value: Box::new(LexTerm::const_int(5)),
            witness: Witness {
                authority: "ofac".to_string(),
                digest: "0xabc".to_string(),
                timestamp: "2026-04-18T10:00:00Z".to_string(),
            },
        };
        let program = compile_lex(&term, &ctx).unwrap();
        let host = FailingProofHost;
        match run_program(&program, &host) {
            crate::interp::EvalResult::Value(v) => {
                // The value operand is still returned even though the
                // attestation call failed.
                assert_eq!(v, serde_json::Value::from(5));
            }
            crate::interp::EvalResult::Error(e) => {
                panic!("Seq aborted on attestation failure; got: {e}")
            }
        }
    }

    #[test]
    fn defeasible_single_exception_nests_match() {
        let ctx = CompileCtx::with_canonical_prelude("demo.defeasible");
        let term = LexTerm::Defeasible {
            name: "demo".to_string(),
            base: Box::new(LexTerm::const_bool(true)),
            exceptions: vec![LexException {
                guard: LexTerm::const_bool(false),
                body: LexTerm::const_bool(false),
                priority: 10,
                source_position: 0,
            }],
        };
        let program = compile_lex(&term, &ctx).unwrap();
        match &program.body[0] {
            Statement::Return(OpExpr::Match { arms, .. }) => {
                assert_eq!(arms.len(), 2);
                assert_eq!(arms[0].pattern, "true");
                assert_eq!(arms[1].pattern, "false");
            }
            other => panic!("expected nested Match, got {other:?}"),
        }
    }
}
