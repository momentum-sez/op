use op_compiler::{compile_yaml, compile_yaml_v1, lower_yaml_v1, LoweringError};

const HISTORICAL_YAML: &str = "operation: different.operation_name\njurisdiction: _default\nversion: '9.0.0'\ndescription: Unrelated description\nsteps:\n  - id: document\n    type: document.board_minutes\n";

fn envelope(purpose: &str, program: &str) -> String {
    let inner = program
        .lines()
        .map(|line| format!("  {line}\n"))
        .collect::<String>();
    format!("version: 1\npurpose: {purpose}\nprogram:\n{inner}")
}

#[test]
fn yaml_compilation_preserves_purpose_without_changing_historical_identity() {
    let yaml = envelope("Entity.Onboarding_v2", HISTORICAL_YAML);
    let result = compile_yaml_v1(&yaml).unwrap();
    assert_eq!(result.purpose().as_str(), "Entity.Onboarding_v2");
    assert_eq!(result.compiled().program.name, "different.operation_name");
    assert_eq!(result.compiled().program.metadata.version, "9.0.0");

    let historical = compile_yaml(HISTORICAL_YAML).unwrap();
    assert_eq!(result.compiled().program, historical.program);
    assert_eq!(
        result.compiled().content_address,
        historical.content_address
    );
    let second = compile_yaml_v1(&envelope("another.purpose", HISTORICAL_YAML)).unwrap();
    assert_eq!(second.purpose().as_str(), "another.purpose");
    assert_eq!(
        second.compiled().content_address,
        historical.content_address
    );
    assert!(compile_yaml_v1(HISTORICAL_YAML).is_err());
    assert!(compile_yaml(&yaml).is_err());
}

#[test]
fn yaml_envelope_rejects_missing_malformed_and_downgraded_purpose_contracts() {
    let valid = envelope("Entity.Onboarding_v2", HISTORICAL_YAML);
    let invalid = [
        valid.replace("version: 1\n", ""),
        valid.replacen("version: 1", "version: 0", 1),
        valid.replacen("version: 1", "version: 2", 1),
        valid.replacen("version: 1", "version: '1'", 1),
        valid.replace("purpose: Entity.Onboarding_v2\n", ""),
        valid.replace("purpose: Entity.Onboarding_v2", "purpose: null"),
        valid.replace("purpose: Entity.Onboarding_v2", "purpose: true"),
        valid.replace("purpose: Entity.Onboarding_v2", "purpose: 123"),
        envelope("'Entity..Onboarding'", HISTORICAL_YAML),
        envelope("' Entity.Onboarding'", HISTORICAL_YAML),
        format!("{valid}purpose_hint: entity.onboarding\n"),
        format!("{valid}purpose: duplicate.purpose\n"),
    ];
    for yaml in invalid {
        assert!(compile_yaml_v1(&yaml).is_err(), "accepted {yaml}");
    }
}

#[test]
fn purpose_envelope_does_not_bypass_inner_sanctions_checks() {
    let unsafe_program = "operation: fiscal.transfer\njurisdiction: _default\nsteps:\n  - id: transfer\n    type: fiscal.transfer\n";
    let error = lower_yaml_v1(&envelope("Fiscal.Transfer", unsafe_program)).unwrap_err();
    match error {
        LoweringError::TypeCheckFailed { errors } => {
            assert!(
                errors.iter().any(|message| message.contains("sanctions")),
                "{errors:?}"
            );
        }
        other => panic!("expected sanctions rejection, got {other}"),
    }
}
