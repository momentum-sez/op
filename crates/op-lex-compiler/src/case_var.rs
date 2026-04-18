//! §6.2 variable rule: `[[Var(n, _)]] = prelude-lookup(n)`.
//!
//! In the admissible fragment, all free variables are prelude-bound. The
//! rule resolves the name against the ambient prelude: a registered value
//! binding lowers to its recorded expression, and an unbound name surfaces
//! as [`CompileError::UnboundVariable`].

use crate::context::CompileCtx;
use crate::error::CompileError;
use op_core::OpExpr;

/// Compile a variable reference.
pub fn compile_var(name: &str, ctx: &CompileCtx) -> Result<OpExpr, CompileError> {
    if let Some((_ty, expr)) = ctx.prelude.lookup_value(name) {
        return Ok(expr.clone());
    }
    // A variable whose name matches a callable lowers to a thunk — an Op
    // `Call` with empty args. The evaluator will error on execution if the
    // callee requires arguments, which is the intended behavior for an
    // improper nullary use.
    if let Some(callable) = ctx.prelude.lookup_callable(name) {
        if let crate::context::PreludeLower::PrimitiveCall { name: pname } = &callable.lower {
            return Ok(OpExpr::Call(pname.clone(), vec![]));
        }
    }
    Err(CompileError::UnboundVariable {
        name: name.to_string(),
    })
}
