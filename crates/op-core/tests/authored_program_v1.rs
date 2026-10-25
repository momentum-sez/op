use op_core::{parse_program, parse_program_v1, AuthoredOpProgramV1};
use serde_json::{json, Value};

const HISTORICAL_PROGRAM: &str = r#"{"name":"different.program_name","jurisdiction":"_default","metadata":{"version":"0.1.0","description":"Unrelated description"},"inputs":[],"outputs":[["result","Bool"]],"effects":[],"participants":[],"approval":null,"contracts":{"requires":[],"ensures":[]},"body":[{"Return":{"Bool":true}}],"gas_budget":{"structural_gas":0,"per_element_gas":0,"cardinality_certificate":null}}"#;

fn envelope() -> Value {
    json!({
        "version": 1,
        "purpose": "Entity.Onboarding_v2",
        "program": serde_json::from_str::<Value>(HISTORICAL_PROGRAM).unwrap(),
    })
}

#[test]
fn authored_parser_preserves_exact_purpose_and_historical_ast_bytes() {
    let authored = parse_program_v1(&envelope().to_string()).unwrap();
    assert_eq!(authored.purpose().as_str(), "Entity.Onboarding_v2");
    assert_eq!(
        serde_json::to_string(authored.program()).unwrap(),
        HISTORICAL_PROGRAM
    );
    let historical = parse_program(HISTORICAL_PROGRAM).unwrap();
    assert_eq!(authored.program(), &historical);
    assert!(parse_program_v1(HISTORICAL_PROGRAM).is_err());
    assert!(parse_program(&envelope().to_string()).is_err());
}

#[test]
fn authored_wire_requires_an_object_and_rejects_duplicate_fields() {
    let object = envelope();
    let parsed = parse_program_v1(&object.to_string()).unwrap();
    assert_eq!(parsed.purpose().as_str(), "Entity.Onboarding_v2");

    let positional = json!([object["version"], object["purpose"], object["program"]]);
    let error = parse_program_v1(&positional.to_string()).unwrap_err();
    assert!(error.to_string().contains("object"), "{error}");

    for field in ["version", "purpose", "program"] {
        let duplicate = format!(
            "{{\"{field}\":{},{}",
            object[field],
            &object.to_string()[1..]
        );
        let error = parse_program_v1(&duplicate).unwrap_err();
        assert!(error.to_string().contains("duplicate field"), "{error}");
        assert!(error.to_string().contains(field), "{error}");
    }
}

#[test]
fn authored_wire_rejects_missing_malformed_downgraded_and_unknown_fields() {
    let mut invalid = Vec::new();
    for field in ["version", "purpose", "program"] {
        let mut value = envelope();
        value.as_object_mut().unwrap().remove(field);
        invalid.push((format!("missing {field}"), value));
    }
    for version in [json!(0), json!(2), json!("1"), Value::Null] {
        let mut value = envelope();
        value["version"] = version;
        invalid.push(("unsupported version".to_string(), value));
    }
    for purpose in [
        json!(""),
        json!(" Entity.onboarding"),
        json!("entity..onboarding"),
        Value::Null,
    ] {
        let mut value = envelope();
        value["purpose"] = purpose;
        invalid.push(("malformed purpose".to_string(), value));
    }
    let mut unknown = envelope();
    unknown["purpose_hint"] = json!("entity.onboarding");
    invalid.push(("unknown field".to_string(), unknown));

    for (case, value) in invalid {
        assert!(
            serde_json::from_value::<AuthoredOpProgramV1>(value).is_err(),
            "accepted {case}"
        );
    }
}

#[test]
fn authored_parser_checks_the_actual_inner_structure_and_types() {
    let mut empty_name = envelope();
    empty_name["program"]["name"] = json!("");
    let error = parse_program_v1(&empty_name.to_string()).unwrap_err();
    assert!(error.to_string().contains("program name cannot be empty"));

    let mut unbound = envelope();
    unbound["program"]["body"] = json!([{"Return": {"Var": "missing_input"}}]);
    let error = parse_program_v1(&unbound.to_string()).unwrap_err();
    assert!(error.to_string().contains("missing_input"));

    let mut wrong_type = envelope();
    wrong_type["program"]["body"] = json!([
        {"Let": {"name": "answer", "ty": "Bool", "value": {"Int": 42}}},
        {"Return": {"Var": "answer"}}
    ]);
    let error = parse_program_v1(&wrong_type.to_string()).unwrap_err();
    assert!(error.to_string().contains("type error:"), "{error}");
}
