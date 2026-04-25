//! A minimal expression interpreter for compiled Op programs.
//!
//! The compilation function lowers each admissible Lex term into an
//! `OpProgram` whose body is `Statement::Return(expr)`. To close the loop
//! for end-to-end verdict equivalence, this interpreter evaluates the
//! compiled expression against an `OpHost` implementation. It covers the
//! subset of Op expressions the six §6.2 cases emit:
//!
//! - Boolean, integer, string, unit literals
//! - `OpExpr::BinOp` / `OpExpr::UnOp` over literal operands
//! - `OpExpr::Record` with field lookup
//! - `OpExpr::List`, `OpExpr::Tuple`
//! - `OpExpr::Call(name, args)` — delegated to the host
//! - `OpExpr::Match` with `tag`-discriminated record scrutinees and boolean
//!   scrutinees
//! - `OpExpr::Field` projection
//!
//! This is not the full Op semantics — linear-resource moves, compensation
//! replay, await suspension, and cross-step composition remain the
//! responsibility of a full Op runtime. The point here is to prove the
//! compiled program is self-consistent enough that a naive evaluator can
//! reproduce the expected verdict.

use op_core::{BinOp, OpExpr, OpHost, OpProgram, Primitive, PrimitiveCall, Statement, UnOp};
use serde_json::Value;
use std::collections::BTreeMap;

/// Evaluation outcome.
#[derive(Debug, Clone, PartialEq)]
pub enum EvalResult {
    /// Reduced to a JSON value.
    Value(Value),
    /// Evaluator aborted.
    Error(String),
}

/// Run a compiled program under a host. Only `Statement::Return` and
/// `Statement::Let` at the top level are recognized — the compiler emits
/// only `Return`.
pub fn run_program(program: &OpProgram, host: &dyn OpHost) -> EvalResult {
    let mut env: BTreeMap<String, Value> = BTreeMap::new();
    for stmt in &program.body {
        match stmt {
            Statement::Return(expr) => {
                return eval_expr(expr, &env, host, &program.jurisdiction);
            }
            Statement::Let { name, value, .. } => {
                match eval_expr(value, &env, host, &program.jurisdiction) {
                    EvalResult::Value(v) => {
                        env.insert(name.clone(), v);
                    }
                    err @ EvalResult::Error(_) => return err,
                }
            }
            other => {
                return EvalResult::Error(format!("unsupported top-level statement: {other:?}"));
            }
        }
    }
    EvalResult::Value(Value::Null)
}

fn eval_expr(
    expr: &OpExpr,
    env: &BTreeMap<String, Value>,
    host: &dyn OpHost,
    jurisdiction: &str,
) -> EvalResult {
    match expr {
        OpExpr::Unit => EvalResult::Value(Value::Null),
        OpExpr::Bool(b) => EvalResult::Value(Value::Bool(*b)),
        OpExpr::Int(i) => EvalResult::Value(Value::from(*i)),
        OpExpr::String(s) => EvalResult::Value(Value::String(s.clone())),
        OpExpr::Null => EvalResult::Value(Value::Null),

        OpExpr::Var(name) => env
            .get(name)
            .cloned()
            .map(EvalResult::Value)
            .unwrap_or_else(|| EvalResult::Error(format!("unbound: {name}"))),

        OpExpr::Record(fields) => {
            let mut out = serde_json::Map::new();
            for (k, e) in fields {
                match eval_expr(e, env, host, jurisdiction) {
                    EvalResult::Value(v) => {
                        out.insert(k.clone(), v);
                    }
                    err @ EvalResult::Error(_) => return err,
                }
            }
            EvalResult::Value(Value::Object(out))
        }

        OpExpr::List(es) => {
            let mut out = Vec::with_capacity(es.len());
            for e in es {
                match eval_expr(e, env, host, jurisdiction) {
                    EvalResult::Value(v) => out.push(v),
                    err @ EvalResult::Error(_) => return err,
                }
            }
            EvalResult::Value(Value::Array(out))
        }

        OpExpr::Tuple(es) => {
            let mut out = Vec::with_capacity(es.len());
            for e in es {
                match eval_expr(e, env, host, jurisdiction) {
                    EvalResult::Value(v) => out.push(v),
                    err @ EvalResult::Error(_) => return err,
                }
            }
            EvalResult::Value(Value::Array(out))
        }

        OpExpr::Field(e, name) => match eval_expr(e, env, host, jurisdiction) {
            EvalResult::Value(Value::Object(m)) => m
                .get(name)
                .cloned()
                .map(EvalResult::Value)
                .unwrap_or_else(|| EvalResult::Error(format!("missing field: {name}"))),
            EvalResult::Value(other) => {
                EvalResult::Error(format!("field on non-record: {other:?}"))
            }
            err => err,
        },

        OpExpr::BinOp(op, a, b) => {
            let va = match eval_expr(a, env, host, jurisdiction) {
                EvalResult::Value(v) => v,
                err => return err,
            };
            let vb = match eval_expr(b, env, host, jurisdiction) {
                EvalResult::Value(v) => v,
                err => return err,
            };
            eval_binop(*op, &va, &vb)
        }

        OpExpr::UnOp(op, a) => {
            let va = match eval_expr(a, env, host, jurisdiction) {
                EvalResult::Value(v) => v,
                err => return err,
            };
            eval_unop(*op, &va)
        }

        OpExpr::Coalesce(a, b) => match eval_expr(a, env, host, jurisdiction) {
            EvalResult::Value(Value::Null) => eval_expr(b, env, host, jurisdiction),
            other => other,
        },

        OpExpr::Seq(a, b) => {
            // Evaluate `a` for its effect, discard its value, return `b`.
            // The left operand is silent only when it succeeds. A failed
            // proof-bundle write is not a tau step; it invalidates the fill.
            match eval_expr(a, env, host, jurisdiction) {
                EvalResult::Value(_) => eval_expr(b, env, host, jurisdiction),
                err @ EvalResult::Error(_) => err,
            }
        }

        OpExpr::Call(name, args) => {
            let mut call_args = BTreeMap::new();
            for (k, e) in args {
                match eval_expr(e, env, host, jurisdiction) {
                    EvalResult::Value(v) => {
                        call_args.insert(k.clone(), v);
                    }
                    err @ EvalResult::Error(_) => return err,
                }
            }
            let call = PrimitiveCall {
                primitive: Primitive(name.clone()),
                args: call_args,
                jurisdiction: jurisdiction.to_string(),
            };
            match host.invoke(&call) {
                Ok(op_core::HostOutcome::Completed(v)) => EvalResult::Value(v),
                Ok(op_core::HostOutcome::Waiting { .. }) => {
                    EvalResult::Error("unexpected waiting outcome".to_string())
                }
                Err(e) => EvalResult::Error(format!("host: {e}")),
            }
        }

        OpExpr::Match {
            scrutinee,
            arms,
            catch_all,
        } => {
            let sv = match eval_expr(scrutinee, env, host, jurisdiction) {
                EvalResult::Value(v) => v,
                err => return err,
            };
            if let Value::Bool(b) = &sv {
                let want = if *b { "true" } else { "false" };
                for arm in arms {
                    if arm.pattern == want {
                        return eval_expr(&arm.body, env, host, jurisdiction);
                    }
                }
                return eval_expr(catch_all, env, host, jurisdiction);
            }
            if let Value::Object(m) = &sv {
                if let Some(Value::String(tag)) = m.get("tag") {
                    for arm in arms {
                        if &arm.pattern == tag {
                            let mut extended = env.clone();
                            if let Some(payload) = m.get("value") {
                                extended.insert(arm.binding.clone(), payload.clone());
                            }
                            return eval_expr(&arm.body, &extended, host, jurisdiction);
                        }
                    }
                }
            }
            eval_expr(catch_all, env, host, jurisdiction)
        }

        other => EvalResult::Error(format!("interp: unsupported expression: {other:?}")),
    }
}

fn eval_binop(op: BinOp, a: &Value, b: &Value) -> EvalResult {
    match op {
        BinOp::Eq => EvalResult::Value(Value::Bool(a == b)),
        BinOp::Ne => EvalResult::Value(Value::Bool(a != b)),
        BinOp::And => match (a.as_bool(), b.as_bool()) {
            (Some(x), Some(y)) => EvalResult::Value(Value::Bool(x && y)),
            _ => EvalResult::Error(format!("and: {a:?} / {b:?}")),
        },
        BinOp::Or => match (a.as_bool(), b.as_bool()) {
            (Some(x), Some(y)) => EvalResult::Value(Value::Bool(x || y)),
            _ => EvalResult::Error(format!("or: {a:?} / {b:?}")),
        },
        BinOp::Lt => int_cmp(a, b, |x, y| x < y),
        BinOp::Le => int_cmp(a, b, |x, y| x <= y),
        BinOp::Gt => int_cmp(a, b, |x, y| x > y),
        BinOp::Ge => int_cmp(a, b, |x, y| x >= y),
        BinOp::Add => int_arith(a, b, |x, y| x + y),
        BinOp::Sub => int_arith(a, b, |x, y| x - y),
        BinOp::Mul => int_arith(a, b, |x, y| x * y),
        BinOp::Contains => match (a, b) {
            (Value::Array(arr), needle) => EvalResult::Value(Value::Bool(arr.contains(needle))),
            (Value::String(s), Value::String(n)) => EvalResult::Value(Value::Bool(s.contains(n))),
            _ => EvalResult::Error(format!("contains: {a:?} / {b:?}")),
        },
        BinOp::In => match (a, b) {
            (needle, Value::Array(arr)) => EvalResult::Value(Value::Bool(arr.contains(needle))),
            _ => EvalResult::Error(format!("in: {a:?} / {b:?}")),
        },
    }
}

fn eval_unop(op: UnOp, a: &Value) -> EvalResult {
    match op {
        UnOp::Not => match a.as_bool() {
            Some(b) => EvalResult::Value(Value::Bool(!b)),
            None => EvalResult::Error(format!("not: {a:?}")),
        },
        UnOp::Neg => match a.as_i64() {
            Some(i) => EvalResult::Value(Value::from(-i)),
            None => EvalResult::Error(format!("neg: {a:?}")),
        },
    }
}

fn int_cmp(a: &Value, b: &Value, f: impl FnOnce(i64, i64) -> bool) -> EvalResult {
    match (a.as_i64(), b.as_i64()) {
        (Some(x), Some(y)) => EvalResult::Value(Value::Bool(f(x, y))),
        _ => EvalResult::Error(format!("cmp: {a:?} / {b:?}")),
    }
}

fn int_arith(a: &Value, b: &Value, f: impl FnOnce(i64, i64) -> i64) -> EvalResult {
    match (a.as_i64(), b.as_i64()) {
        (Some(x), Some(y)) => EvalResult::Value(Value::from(f(x, y))),
        _ => EvalResult::Error(format!("arith: {a:?} / {b:?}")),
    }
}
