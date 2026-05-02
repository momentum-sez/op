//! JSON wire-format parser.
//!
//! Op programs serialize to JSON through the `serde` derivation on the AST
//! types. This module validates structural integrity on the way in, and
//! supplies convenience helpers for parsing programs and standalone steps.
//!
//! A surface-syntax parser is beyond the scope of this crate: Op programs
//! authored through the source surface are typically lowered by the
//! `op-compiler` crate, which converts YAML operation definitions (or a
//! future concrete-syntax grammar) into the AST types defined here.

use crate::ast::{OpExpr, OpProgram, OpStep, Statement};
use crate::error::OpError;

/// Parse an `OpProgram` from its JSON wire form.
pub fn parse_program(source: &str) -> Result<OpProgram, OpError> {
    let program: OpProgram = serde_json::from_str(source).map_err(|e| OpError::ParseError {
        line: e.line(),
        message: format!("JSON parse: {e}"),
    })?;
    if program.name.is_empty() {
        return Err(OpError::ParseError {
            line: 0,
            message: "program name cannot be empty".to_string(),
        });
    }
    if program.jurisdiction.is_empty() {
        return Err(OpError::ParseError {
            line: 0,
            message: "program jurisdiction cannot be empty (use \"_default\" for generic)"
                .to_string(),
        });
    }
    validate_block(&program.body)?;
    Ok(program)
}

/// Parse a single `OpStep` from its JSON wire form.
pub fn parse_step(source: &str) -> Result<OpStep, OpError> {
    let step: OpStep = serde_json::from_str(source).map_err(|e| OpError::ParseError {
        line: e.line(),
        message: format!("JSON parse: {e}"),
    })?;
    if step.id.is_empty() {
        return Err(OpError::ParseError {
            line: 0,
            message: "step id cannot be empty".to_string(),
        });
    }
    Ok(step)
}

fn validate_block(block: &[Statement]) -> Result<(), OpError> {
    for stmt in block {
        validate_statement(stmt)?;
    }
    Ok(())
}

fn validate_statement(stmt: &Statement) -> Result<(), OpError> {
    match stmt {
        Statement::Let { name, value, .. } => {
            if name.is_empty() {
                return Err(OpError::ParseError {
                    line: 0,
                    message: "let binding must have a name".to_string(),
                });
            }
            validate_expr(value)
        }
        Statement::Run { name, call } => {
            if name.is_empty() {
                return Err(OpError::ParseError {
                    line: 0,
                    message: "run binding must have a name".to_string(),
                });
            }
            validate_expr(call)
        }
        Statement::Step(step) => {
            if step.id.is_empty() {
                return Err(OpError::ParseError {
                    line: 0,
                    message: "step must have an id".to_string(),
                });
            }
            match &step.body {
                crate::ast::StepBody::Primitive(_, args) => {
                    for (_, e) in args {
                        validate_expr(e)?;
                    }
                }
                crate::ast::StepBody::Block(inner) => validate_block(inner)?,
            }
            if let Some(comp) = &step.compensate {
                match &comp.body {
                    crate::ast::StepBody::Primitive(_, args) => {
                        for (_, e) in args {
                            validate_expr(e)?;
                        }
                    }
                    crate::ast::StepBody::Block(inner) => validate_block(inner)?,
                }
            }
            Ok(())
        }
        Statement::Par { branches } => {
            for (_, e) in branches {
                validate_expr(e)?;
            }
            Ok(())
        }
        Statement::Choose { arms, else_block } => {
            for (guard, branch) in arms {
                validate_expr(guard)?;
                validate_block(branch)?;
            }
            if let Some(e) = else_block {
                validate_block(e)?;
            }
            Ok(())
        }
        Statement::In { body, .. } => validate_block(body),
        Statement::Policy { name, .. } => {
            if name.is_empty() {
                return Err(OpError::ParseError {
                    line: 0,
                    message: "policy block must have a name".to_string(),
                });
            }
            Ok(())
        }
        Statement::Return(e) | Statement::Expr(e) => validate_expr(e),
    }
}

fn validate_expr(expr: &OpExpr) -> Result<(), OpError> {
    match expr {
        OpExpr::Record(fields) => {
            for (_, e) in fields {
                validate_expr(e)?;
            }
            Ok(())
        }
        OpExpr::List(items) | OpExpr::Tuple(items) => {
            for item in items {
                validate_expr(item)?;
            }
            Ok(())
        }
        OpExpr::Call(name, args) => {
            if name.is_empty() {
                return Err(OpError::ParseError {
                    line: 0,
                    message: "call expression must have a function name".to_string(),
                });
            }
            for (_, e) in args {
                validate_expr(e)?;
            }
            Ok(())
        }
        OpExpr::BinOp(_, a, b) | OpExpr::Coalesce(a, b) | OpExpr::Seq(a, b) => {
            validate_expr(a)?;
            validate_expr(b)
        }
        OpExpr::UnOp(_, a) | OpExpr::Field(a, _) => validate_expr(a),
        OpExpr::Match {
            scrutinee,
            arms,
            catch_all,
        } => {
            validate_expr(scrutinee)?;
            for arm in arms {
                validate_expr(&arm.body)?;
            }
            validate_expr(catch_all)
        }
        OpExpr::ConsumeLinear(inner) => validate_expr(inner),
        OpExpr::Lock { resource, .. } => validate_expr(resource),
        OpExpr::CommitTransfer { locked, witness } | OpExpr::ReleaseLock { locked, witness } => {
            validate_expr(locked)?;
            validate_expr(witness)
        }
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;

    #[test]
    fn round_trip_trivial_program() {
        let prog = OpProgram {
            name: "t.op".to_string(),
            jurisdiction: "_default".to_string(),
            metadata: ProgramMetadata::default(),
            inputs: vec![],
            outputs: vec![],
            effects: vec![Effect::Pure],
            participants: vec![],
            approval: None,
            contracts: Contracts::default(),
            body: vec![Statement::Return(OpExpr::Int(42))],
            gas_budget: GasBudget::default(),
        };
        let json = serde_json::to_string(&prog).unwrap();
        let parsed = parse_program(&json).unwrap();
        assert_eq!(parsed.name, "t.op");
    }

    #[test]
    fn reject_empty_name() {
        let prog = OpProgram {
            name: "".to_string(),
            jurisdiction: "_default".to_string(),
            metadata: ProgramMetadata::default(),
            inputs: vec![],
            outputs: vec![],
            effects: vec![],
            participants: vec![],
            approval: None,
            contracts: Contracts::default(),
            body: vec![],
            gas_budget: GasBudget::default(),
        };
        let json = serde_json::to_string(&prog).unwrap();
        assert!(parse_program(&json).is_err());
    }

    #[test]
    fn reject_empty_jurisdiction() {
        let prog = OpProgram {
            name: "x".to_string(),
            jurisdiction: "".to_string(),
            metadata: ProgramMetadata::default(),
            inputs: vec![],
            outputs: vec![],
            effects: vec![],
            participants: vec![],
            approval: None,
            contracts: Contracts::default(),
            body: vec![],
            gas_budget: GasBudget::default(),
        };
        let json = serde_json::to_string(&prog).unwrap();
        assert!(parse_program(&json).is_err());
    }

    #[test]
    fn reject_call_with_empty_name() {
        let prog = OpProgram {
            name: "x".to_string(),
            jurisdiction: "_default".to_string(),
            metadata: ProgramMetadata::default(),
            inputs: vec![],
            outputs: vec![],
            effects: vec![],
            participants: vec![],
            approval: None,
            contracts: Contracts::default(),
            body: vec![Statement::Return(OpExpr::Call(String::new(), vec![]))],
            gas_budget: GasBudget::default(),
        };
        let json = serde_json::to_string(&prog).unwrap();
        assert!(parse_program(&json).is_err());
    }

    #[test]
    fn parse_standalone_step() {
        let step = OpStep {
            id: "create".to_string(),
            body: StepBody::Primitive(Primitive("create.entity".to_string()), vec![]),
            signature: StepSignature {
                input: OpType::Unit,
                output: OpType::EntityRef,
                effects: vec![Effect::SovereignWrite],
            },
            wait: None,
            on_failure: None,
            compensate: None,
            contracts: Contracts::default(),
        };
        let json = serde_json::to_string(&step).unwrap();
        assert_eq!(parse_step(&json).unwrap().id, "create");
    }
}
