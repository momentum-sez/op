//! Gas model — two-tier.
//!
//! - **Structural gas** is a static bound on the program skeleton. It is paid
//!   at compile time when the type checker walks the AST and assigns each
//!   construct a constant cost.
//! - **Extensional gas** is a runtime cost proportional to the cardinalities
//!   the evaluator actually encounters (list length, record field count,
//!   syscall volume, storage growth). Certain programs may pin their
//!   extensional gas via a cardinality certificate.

use crate::ast::{CardinalityCertificate, Statement};
use crate::error::OpError;
use serde::{Deserialize, Serialize};

/// Gas configuration — per-evaluation limits.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GasConfig {
    /// Maximum structural gas.
    pub structural_limit: u64,
    /// Maximum extensional gas.
    pub extensional_limit: u64,
}

impl Default for GasConfig {
    fn default() -> Self {
        Self {
            structural_limit: 1_000_000,
            extensional_limit: 10_000_000,
        }
    }
}

/// A live gas meter.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GasMeter {
    /// Structural gas consumed so far.
    pub structural_used: u64,
    /// Extensional gas consumed so far.
    pub extensional_used: u64,
    /// Configured limits.
    pub config: GasConfig,
}

impl GasMeter {
    /// Construct a new meter against a configuration.
    pub fn new(config: GasConfig) -> Self {
        Self {
            structural_used: 0,
            extensional_used: 0,
            config,
        }
    }

    /// Charge structural gas. Saturating addition prevents overflow.
    pub fn charge_structural(&mut self, amount: u64) -> Result<(), OpError> {
        let new = self.structural_used.saturating_add(amount);
        if new > self.config.structural_limit {
            return Err(OpError::GasLimitExceeded {
                used: new,
                limit: self.config.structural_limit,
            });
        }
        self.structural_used = new;
        Ok(())
    }

    /// Charge extensional gas.
    pub fn charge_extensional(&mut self, amount: u64) -> Result<(), OpError> {
        let new = self.extensional_used.saturating_add(amount);
        if new > self.config.extensional_limit {
            return Err(OpError::GasLimitExceeded {
                used: new,
                limit: self.config.extensional_limit,
            });
        }
        self.extensional_used = new;
        Ok(())
    }
}

/// Static estimate derived at compile time.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct GasEstimate {
    /// Static structural gas bound.
    pub structural_gas: u64,
    /// Extensional gas bound (if a cardinality certificate is attached).
    pub extensional_gas_bound: Option<u64>,
    /// Whether the compiler requires a runtime cardinality certificate.
    pub needs_cardinality_cert: bool,
}

/// Per-construct structural cost table. Kept in one place so host embedders
/// can override the table for their deployment.
#[derive(Debug, Clone, Copy)]
pub struct StructuralCostTable {
    /// Cost of a let-binding.
    pub let_cost: u64,
    /// Cost of a step declaration.
    pub step_cost: u64,
    /// Cost of a run statement.
    pub run_cost: u64,
    /// Cost of a parallel branch.
    pub par_branch_cost: u64,
    /// Cost of a choose arm.
    pub choose_arm_cost: u64,
    /// Cost of an `in <jurisdiction>` scope.
    pub in_scope_cost: u64,
    /// Cost of a policy block.
    pub policy_cost: u64,
    /// Cost of a return.
    pub return_cost: u64,
    /// Cost of a naked expression statement.
    pub expr_cost: u64,
}

impl Default for StructuralCostTable {
    fn default() -> Self {
        Self {
            let_cost: 1,
            step_cost: 10,
            run_cost: 10,
            par_branch_cost: 2,
            choose_arm_cost: 2,
            in_scope_cost: 1,
            policy_cost: 5,
            return_cost: 1,
            expr_cost: 1,
        }
    }
}

/// Walk a program body and return a static structural gas bound.
pub fn estimate_structural_gas(
    body: &[Statement],
    table: StructuralCostTable,
) -> u64 {
    let mut total: u64 = 0;
    for stmt in body {
        total = total.saturating_add(statement_cost(stmt, table));
    }
    total
}

fn statement_cost(stmt: &Statement, table: StructuralCostTable) -> u64 {
    match stmt {
        Statement::Let { .. } => table.let_cost,
        Statement::Run { .. } => table.run_cost,
        Statement::Step(step) => {
            let mut c = table.step_cost;
            if let crate::ast::StepBody::Block(inner) = &step.body {
                c = c.saturating_add(estimate_structural_gas(inner, table));
            }
            if let Some(comp) = &step.compensate {
                if let crate::ast::StepBody::Block(inner) = &comp.body {
                    c = c.saturating_add(estimate_structural_gas(inner, table));
                }
            }
            c
        }
        Statement::Par { branches } => branches
            .iter()
            .fold(0u64, |acc, _| acc.saturating_add(table.par_branch_cost)),
        Statement::Choose { arms, else_block } => {
            let mut c: u64 = 0;
            for (_guard, branch) in arms {
                c = c.saturating_add(table.choose_arm_cost);
                c = c.saturating_add(estimate_structural_gas(branch, table));
            }
            if let Some(else_body) = else_block {
                c = c.saturating_add(estimate_structural_gas(else_body, table));
            }
            c
        }
        Statement::In { body, .. } => {
            let c = table.in_scope_cost;
            c.saturating_add(estimate_structural_gas(body, table))
        }
        Statement::Policy { .. } => table.policy_cost,
        Statement::Return(_) => table.return_cost,
        Statement::Expr(_) => table.expr_cost,
    }
}

/// Compute the extensional gas bound if a certificate is attached.
///
/// Given `per_element_gas * cardinality`, returns the bound; returns `None`
/// when the certificate is absent.
pub fn extensional_bound(per_element: u64, cert: Option<&CardinalityCertificate>) -> Option<u64> {
    let c = cert?;
    Some(per_element.saturating_mul(c.cardinality))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        Contracts, Effect, GasBudget, OpExpr, OpProgram, OpStep, OpType, Primitive, ProgramMetadata,
        StepBody, StepSignature,
    };

    #[test]
    fn meter_charges_and_fails_at_limit() {
        let mut m = GasMeter::new(GasConfig {
            structural_limit: 100,
            extensional_limit: 100,
        });
        assert!(m.charge_structural(50).is_ok());
        assert!(m.charge_structural(60).is_err());
    }

    #[test]
    fn structural_estimate_walks_body() {
        let body = vec![
            Statement::Let {
                name: "x".to_string(),
                ty: OpType::Int,
                value: OpExpr::Int(1),
            },
            Statement::Step(OpStep {
                id: "s1".to_string(),
                body: StepBody::Primitive(Primitive("noop".to_string()), vec![]),
                signature: StepSignature {
                    input: OpType::Unit,
                    output: OpType::Unit,
                    effects: vec![Effect::Pure],
                },
                wait: None,
                on_failure: None,
                compensate: None,
                contracts: Contracts::default(),
            }),
        ];
        let cost = estimate_structural_gas(&body, StructuralCostTable::default());
        assert!(cost >= 11);
    }

    #[test]
    fn program_total_structural_gas() {
        let prog = OpProgram {
            name: "t".to_string(),
            jurisdiction: "_default".to_string(),
            metadata: ProgramMetadata::default(),
            inputs: vec![],
            outputs: vec![],
            effects: vec![],
            participants: vec![],
            approval: None,
            contracts: Contracts::default(),
            body: vec![Statement::Return(OpExpr::Unit)],
            gas_budget: GasBudget::default(),
        };
        let cost = estimate_structural_gas(&prog.body, StructuralCostTable::default());
        assert_eq!(cost, 1);
    }
}
