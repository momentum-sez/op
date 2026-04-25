//! Compensation runtime — failure-path inverse execution.
//!
//! A two-step program commits step 1 then fails on step 2. The
//! expected behavior is that step 1's compensation (its `inverse`)
//! executes exactly once, in reverse topological order relative to
//! the committed prefix.
//!
//! The Op AST supplies the `CompensationClause` declaration shape at
//! the language level; this crate does not ship a full step-execution
//! runtime. The test embeds a minimal deterministic executor over the
//! typed AST, walks the body of the program, and records callback
//! order into a `Vec<String>` owned by the host. The assertion is a
//! structural claim about what the compensation machinery must do:
//!
//!   1. Commit steps forward in source order until one fails.
//!   2. On failure, walk back over the committed prefix in reverse
//!      source order, dispatching each step's `compensate` body to
//!      the host.
//!   3. Dispatch each compensation exactly once.

use op_core::{
    CompensationClause, Contracts, Effect, GasBudget, OpHost, OpProgram, OpStep, OpType, Primitive,
    PrimitiveCall, ProgramMetadata, Statement, StepBody, StepSignature,
};
use std::sync::{Arc, Mutex};

/// Host that records invocation order and can be configured to fail a
/// specific primitive with a `Permanent` error.
#[derive(Clone)]
struct RecordingHost {
    /// Ordered sequence of primitive names invoked against this host.
    trail: Arc<Mutex<Vec<String>>>,
    /// Primitive name that triggers a permanent failure on first call.
    fail_on: String,
}

impl RecordingHost {
    fn new(fail_on: &str) -> Self {
        Self {
            trail: Arc::new(Mutex::new(Vec::new())),
            fail_on: fail_on.to_string(),
        }
    }

    fn trail(&self) -> Vec<String> {
        self.trail.lock().unwrap().clone()
    }
}

impl OpHost for RecordingHost {
    fn invoke(&self, call: &PrimitiveCall) -> Result<op_core::HostOutcome, op_core::HostError> {
        let name = call.primitive.0.clone();
        self.trail.lock().unwrap().push(name.clone());
        if name == self.fail_on {
            return Err(op_core::HostError::Permanent(format!(
                "simulated failure on {name}"
            )));
        }
        Ok(op_core::HostOutcome::Completed(serde_json::Value::Null))
    }
}

/// Minimal forward-commit / reverse-compensate walker over an OpProgram
/// body, emitting exactly the semantics required of a compensation
/// runtime. Returns `Ok(())` on full success, `Err(String)` on failure
/// after all relevant compensations have run.
fn run_with_compensation(program: &OpProgram, host: &RecordingHost) -> Result<(), String> {
    let mut committed: Vec<&OpStep> = Vec::new();
    let mut failure: Option<String> = None;

    for stmt in &program.body {
        let Statement::Step(step) = stmt else {
            continue;
        };

        let call = match &step.body {
            StepBody::Primitive(p, args) => {
                let mut a = std::collections::BTreeMap::new();
                for (k, _) in args {
                    a.insert(k.clone(), serde_json::Value::Null);
                }
                PrimitiveCall {
                    primitive: p.clone(),
                    args: a,
                    jurisdiction: program.jurisdiction.clone(),
                }
            }
            StepBody::Block(_) => continue,
        };

        match host.invoke(&call) {
            Ok(_) => {
                committed.push(step);
            }
            Err(e) => {
                failure = Some(format!("{e}"));
                break;
            }
        }
    }

    if let Some(err) = failure {
        // Reverse topological order: walk the committed prefix back.
        for step in committed.iter().rev() {
            if let Some(comp) = &step.compensate {
                if let StepBody::Primitive(p, args) = &comp.body {
                    let mut a = std::collections::BTreeMap::new();
                    for (k, _) in args {
                        a.insert(k.clone(), serde_json::Value::Null);
                    }
                    let call = PrimitiveCall {
                        primitive: p.clone(),
                        args: a,
                        jurisdiction: program.jurisdiction.clone(),
                    };
                    // Compensation calls bypass the failure trigger on
                    // their own pathway — the test assertion is on order,
                    // not on the behavior of a failing inverse.
                    let _ = host.invoke(&call);
                }
            }
        }
        return Err(err);
    }
    Ok(())
}

fn build_two_step_program() -> OpProgram {
    let step1 = OpStep {
        id: "book_reservation".to_string(),
        body: StepBody::Primitive(Primitive("booking.reserve".to_string()), vec![]),
        signature: StepSignature {
            input: OpType::Unit,
            output: OpType::Unit,
            effects: vec![Effect::SanctionsCheck, Effect::SovereignWrite],
        },
        wait: None,
        on_failure: None,
        compensate: Some(CompensationClause {
            body: StepBody::Primitive(Primitive("booking.cancel_reservation".to_string()), vec![]),
            invalidated_domains: vec![],
        }),
        contracts: Contracts::default(),
    };
    let step2 = OpStep {
        id: "commit_transfer".to_string(),
        body: StepBody::Primitive(Primitive("fiscal.transfer".to_string()), vec![]),
        signature: StepSignature {
            input: OpType::Unit,
            output: OpType::Unit,
            effects: vec![Effect::FiscalTransfer],
        },
        wait: None,
        on_failure: Some(op_core::FailureAction::CancelOperation),
        compensate: Some(CompensationClause {
            body: StepBody::Primitive(Primitive("fiscal.reverse_transfer".to_string()), vec![]),
            invalidated_domains: vec![],
        }),
        contracts: Contracts::default(),
    };
    OpProgram {
        name: "two_step_with_compensation".to_string(),
        jurisdiction: "_default".to_string(),
        metadata: ProgramMetadata::default(),
        inputs: vec![],
        outputs: vec![],
        effects: vec![
            Effect::SanctionsCheck,
            Effect::SovereignWrite,
            Effect::FiscalTransfer,
        ],
        participants: vec![],
        approval: None,
        contracts: op_core::Contracts::default(),
        body: vec![Statement::Step(step1), Statement::Step(step2)],
        gas_budget: GasBudget::default(),
    }
}

#[test]
fn step1_compensation_runs_once_on_step2_failure() {
    let program = build_two_step_program();
    // Fail step 2 — fiscal.transfer — after step 1 has committed.
    let host = RecordingHost::new("fiscal.transfer");
    let outcome = run_with_compensation(&program, &host);
    assert!(outcome.is_err(), "expected failure on step 2");

    let trail = host.trail();
    // Expected: step 1 forward (reserve), step 2 forward (fails),
    // step 1's inverse (cancel_reservation) exactly once.
    assert_eq!(
        trail,
        vec![
            "booking.reserve".to_string(),
            "fiscal.transfer".to_string(),
            "booking.cancel_reservation".to_string(),
        ],
        "compensation order incorrect: {trail:?}"
    );

    // Exactly-once discipline.
    let inverse_hits = trail
        .iter()
        .filter(|n| *n == "booking.cancel_reservation")
        .count();
    assert_eq!(
        inverse_hits, 1,
        "compensation fired {inverse_hits} times; expected 1"
    );
}

#[test]
fn reverse_topological_order_on_three_steps() {
    // Extend the program with a third step that fails. Compensations
    // must fire in the order (step_2_inverse, step_1_inverse) — the
    // reverse of the committed prefix.
    let mut program = build_two_step_program();
    // Relabel step 2 so it commits successfully; insert a new failing
    // step 3.
    if let Statement::Step(s2) = &mut program.body[1] {
        s2.body = StepBody::Primitive(Primitive("fiscal.transfer_ok".to_string()), vec![]);
    }
    let step3 = OpStep {
        id: "attest".to_string(),
        body: StepBody::Primitive(Primitive("attestation.emit".to_string()), vec![]),
        signature: StepSignature {
            input: OpType::Unit,
            output: OpType::Unit,
            effects: vec![Effect::ProofEmit],
        },
        wait: None,
        on_failure: Some(op_core::FailureAction::CancelOperation),
        compensate: None,
        contracts: Contracts::default(),
    };
    program.body.push(Statement::Step(step3));

    let host = RecordingHost::new("attestation.emit");
    let outcome = run_with_compensation(&program, &host);
    assert!(outcome.is_err());

    let trail = host.trail();
    // Committed prefix: step 1, step 2. Step 3 fails. Compensations
    // fire in reverse: step 2's inverse, then step 1's inverse.
    assert_eq!(
        trail,
        vec![
            "booking.reserve".to_string(),
            "fiscal.transfer_ok".to_string(),
            "attestation.emit".to_string(),
            "fiscal.reverse_transfer".to_string(),
            "booking.cancel_reservation".to_string(),
        ],
        "reverse topological order violated: {trail:?}"
    );
}
