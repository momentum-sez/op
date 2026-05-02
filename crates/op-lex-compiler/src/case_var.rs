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
    if ctx.lookup_binder(name).is_some() {
        return Ok(OpExpr::Var(name.to_string()));
    }
    if let Some((_ty, expr)) = ctx.prelude.lookup_value(name) {
        return Ok(expr.clone());
    }
    Err(CompileError::UnboundVariable {
        name: name.to_string(),
    })
}
