//! §6.2 constant rule: `[[Const(v)]] = literal(lift_value(v))`.
//!
//! The mapping is pointwise: a Lex base value lifts into the corresponding
//! Op expression via [`crate::lift::lift_value`].

use crate::ast::LexValue;
use crate::lift::lift_value;
use op_core::OpExpr;

/// Compile a Lex constant into an Op expression literal.
pub fn compile_const(value: &LexValue) -> OpExpr {
    lift_value(value)
}
