//! Value lifting — `lift_value : LexValue -> OpExpr`.
//!
//! Each Lex base constructor maps to the corresponding Op expression shape.
//! The mapping is structural and total on `LexValue`.

use crate::ast::LexValue;
use op_core::OpExpr;

/// Map a Lex base value to an Op expression.
pub fn lift_value(v: &LexValue) -> OpExpr {
    match v {
        LexValue::Bool(b) => OpExpr::Bool(*b),
        LexValue::Int(i) => OpExpr::Int(*i),
        LexValue::Str(s) => OpExpr::String(s.clone()),
        LexValue::Unit => OpExpr::Unit,
        LexValue::Record(fields) => OpExpr::Record(
            fields
                .iter()
                .map(|(k, fv)| (k.clone(), lift_value(fv)))
                .collect(),
        ),
        LexValue::List(elems) => OpExpr::List(elems.iter().map(lift_value).collect()),
        LexValue::Variant { tag, payload } => {
            // Encode as a record `{ tag, value }` — the Op AST does not
            // carry a surface variant expression, so we normalize to the
            // record shape Op's host already knows.
            OpExpr::Record(vec![
                ("tag".to_string(), OpExpr::String(tag.clone())),
                ("value".to_string(), lift_value(payload)),
            ])
        }
    }
}
