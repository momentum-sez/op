//! Proof-bundle determinism — byte-identical execution under a
//! deterministic host and fixed inputs.
//!
//! Executing the same `OpProgram` twice with a fixed oracle log and
//! fixed inputs produces byte-identical proof bundles. The bundle
//! shape exercised here is the minimum a structural executor emits:
//! ordered primitive invocations paired with their outcomes, keyed by
//! step id. The serialization uses the canonical `serde_json` wire
//! form — a deterministic encoder on a BTreeMap-backed structure.
//!
//! A proof-bundle digest is the SHA-256 of the bundle's canonical
//! bytes. Determinism is the equality of two such digests across two
//! independent runs.

use op_core::{
    Contracts, Effect, GasBudget, OpExpr, OpHost, OpProgram, OpStep, OpType, Primitive,
    PrimitiveCall, ProgramMetadata, Statement, StepBody, StepSignature,
};
use std::collections::BTreeMap;

/// A deterministic host driven by a fixed oracle: each call maps to a
/// pre-declared outcome by primitive name.
struct FixedOracleHost {
    oracle: BTreeMap<String, serde_json::Value>,
}

impl FixedOracleHost {
    fn new(oracle: BTreeMap<String, serde_json::Value>) -> Self {
        Self { oracle }
    }
}

impl OpHost for FixedOracleHost {
    fn invoke(
        &self,
        call: &PrimitiveCall,
    ) -> Result<op_core::HostOutcome, op_core::HostError> {
        match self.oracle.get(&call.primitive.0) {
            Some(v) => Ok(op_core::HostOutcome::Completed(v.clone())),
            None => Err(op_core::HostError::UnknownPrimitive(call.primitive.0.clone())),
        }
    }
}

/// One step's record in the proof bundle. Ordered deterministically
/// by the execution walker.
#[derive(serde::Serialize)]
struct BundleEntry {
    step: String,
    primitive: String,
    args: BTreeMap<String, serde_json::Value>,
    outcome: serde_json::Value,
}

/// Canonical proof-bundle serialization: the program digest concept
/// reduced to its minimum — ordered step records with their inputs
/// and outputs.
#[derive(serde::Serialize)]
struct ProofBundle {
    program: String,
    jurisdiction: String,
    entries: Vec<BundleEntry>,
}

fn execute_and_bundle(program: &OpProgram, host: &dyn OpHost) -> ProofBundle {
    let mut entries: Vec<BundleEntry> = Vec::new();
    for stmt in &program.body {
        let Statement::Step(step) = stmt else { continue };
        let (prim, arg_pairs) = match &step.body {
            StepBody::Primitive(p, args) => (p.clone(), args.clone()),
            StepBody::Block(_) => continue,
        };

        // Reduce arguments deterministically: literal OpExprs → JSON.
        let mut reduced: BTreeMap<String, serde_json::Value> = BTreeMap::new();
        for (k, e) in &arg_pairs {
            reduced.insert(k.clone(), reduce_expr(e));
        }

        let call = PrimitiveCall {
            primitive: prim.clone(),
            args: reduced.clone(),
            jurisdiction: program.jurisdiction.clone(),
        };

        let outcome = match host.invoke(&call) {
            Ok(op_core::HostOutcome::Completed(v)) => v,
            Ok(op_core::HostOutcome::Waiting { event, .. }) => {
                serde_json::json!({ "waiting": event })
            }
            Err(e) => serde_json::json!({ "error": format!("{e}") }),
        };

        entries.push(BundleEntry {
            step: step.id.clone(),
            primitive: prim.0.clone(),
            args: reduced,
            outcome,
        });
    }
    ProofBundle {
        program: program.name.clone(),
        jurisdiction: program.jurisdiction.clone(),
        entries,
    }
}

fn reduce_expr(e: &OpExpr) -> serde_json::Value {
    match e {
        OpExpr::Unit | OpExpr::Null => serde_json::Value::Null,
        OpExpr::Bool(b) => serde_json::Value::Bool(*b),
        OpExpr::Int(i) => serde_json::Value::from(*i),
        OpExpr::String(s) => serde_json::Value::String(s.clone()),
        _ => serde_json::Value::Null,
    }
}

/// Byte-level canonical encoding: `serde_json::to_vec` on a
/// structure with explicit field order.
fn canonical_bytes(bundle: &ProofBundle) -> Vec<u8> {
    serde_json::to_vec(bundle).expect("bundle serializes")
}

/// SHA-256-flavored digest: for determinism we only need a stable
/// byte fingerprint. The test uses the canonical bytes directly —
/// equality of bytes is a stricter claim than equality of digests.
fn digest(bundle: &ProofBundle) -> Vec<u8> {
    canonical_bytes(bundle)
}

fn three_step_program() -> OpProgram {
    let s1 = OpStep {
        id: "screen".to_string(),
        body: StepBody::Primitive(
            Primitive("sanctions.check".to_string()),
            vec![(
                "principal".to_string(),
                OpExpr::String("entity-0xabc".to_string()),
            )],
        ),
        signature: StepSignature {
            input: OpType::EntityRef,
            output: OpType::Bool,
            effects: vec![Effect::SanctionsCheck],
        },
        wait: None,
        on_failure: None,
        compensate: None,
        contracts: Contracts::default(),
    };
    let s2 = OpStep {
        id: "threshold".to_string(),
        body: StepBody::Primitive(
            Primitive("fiscal.threshold_check".to_string()),
            vec![
                ("amount".to_string(), OpExpr::Int(42)),
                ("threshold".to_string(), OpExpr::Int(100)),
            ],
        ),
        signature: StepSignature {
            input: OpType::Record(vec![]),
            output: OpType::Bool,
            effects: vec![Effect::Pure],
        },
        wait: None,
        on_failure: None,
        compensate: None,
        contracts: Contracts::default(),
    };
    let s3 = OpStep {
        id: "attest".to_string(),
        body: StepBody::Primitive(
            Primitive("attestation.emit".to_string()),
            vec![
                ("digest".to_string(), OpExpr::String("0xdeadbeef".to_string())),
            ],
        ),
        signature: StepSignature {
            input: OpType::Unit,
            output: OpType::Unit,
            effects: vec![Effect::ProofEmit],
        },
        wait: None,
        on_failure: None,
        compensate: None,
        contracts: Contracts::default(),
    };
    OpProgram {
        name: "deterministic.three_step".to_string(),
        jurisdiction: "_default".to_string(),
        metadata: ProgramMetadata::default(),
        inputs: vec![],
        outputs: vec![],
        effects: vec![Effect::SanctionsCheck, Effect::ProofEmit],
        participants: vec![],
        approval: None,
        contracts: Contracts::default(),
        body: vec![Statement::Step(s1), Statement::Step(s2), Statement::Step(s3)],
        gas_budget: GasBudget::default(),
    }
}

fn fixed_oracle() -> BTreeMap<String, serde_json::Value> {
    let mut oracle = BTreeMap::new();
    oracle.insert("sanctions.check".to_string(), serde_json::Value::Bool(true));
    oracle.insert(
        "fiscal.threshold_check".to_string(),
        serde_json::Value::Bool(false),
    );
    oracle.insert(
        "attestation.emit".to_string(),
        serde_json::json!({"id": "att-1"}),
    );
    oracle
}

#[test]
fn two_runs_produce_byte_identical_bundles() {
    let program = three_step_program();

    let host_a = FixedOracleHost::new(fixed_oracle());
    let bundle_a = execute_and_bundle(&program, &host_a);
    let bytes_a = digest(&bundle_a);

    let host_b = FixedOracleHost::new(fixed_oracle());
    let bundle_b = execute_and_bundle(&program, &host_b);
    let bytes_b = digest(&bundle_b);

    assert_eq!(
        bytes_a, bytes_b,
        "proof bundle bytes diverged across runs: {} vs {}",
        String::from_utf8_lossy(&bytes_a),
        String::from_utf8_lossy(&bytes_b)
    );
}

#[test]
fn permuted_oracle_keys_do_not_perturb_bundle() {
    // The oracle map uses BTreeMap so key order is canonical; the
    // bundle walker iterates program body in declared order; and
    // the argument records use BTreeMap already. The determinism
    // claim therefore holds regardless of the order in which the
    // oracle is populated.
    let program = three_step_program();

    let host_a = FixedOracleHost::new(fixed_oracle());
    // Re-insert keys in a different order — BTreeMap canonicalizes.
    let mut oracle_perm = BTreeMap::new();
    oracle_perm.insert(
        "attestation.emit".to_string(),
        serde_json::json!({"id": "att-1"}),
    );
    oracle_perm.insert(
        "fiscal.threshold_check".to_string(),
        serde_json::Value::Bool(false),
    );
    oracle_perm.insert("sanctions.check".to_string(), serde_json::Value::Bool(true));
    let host_b = FixedOracleHost::new(oracle_perm);

    let bytes_a = digest(&execute_and_bundle(&program, &host_a));
    let bytes_b = digest(&execute_and_bundle(&program, &host_b));

    assert_eq!(bytes_a, bytes_b);
}
