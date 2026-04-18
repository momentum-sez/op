//! §6.2 sanctions-dominance rule:
//!
//! ```text
//!   [[SanctionsDominance(p)]] =
//!     call("sanctions.check", { principal: [[p]] })
//! ```
//!
//! The emitted expression invokes the host primitive `sanctions.check`. The
//! host returns a tagged value: `{ tag: "Compliant", value: () }` or
//! `{ tag: "SanctionsBlocked", value: { list, digest } }`. The sanctions-
//! bottom semantics — a sanctions-blocked principal dominates every other
//! verdict in the residual pipeline — is enforced in the host, not in the
//! compiler. The compiler guarantees that any path reaching a committing
//! effect (sovereign write, fiscal transfer) in the compiled program is
//! dominated by a `sanctions.check` invocation; see §3.9 of the Op language
//! reference.

use crate::context::CompileCtx;
use op_core::OpExpr;

/// Compile a sanctions-dominance term.
pub fn compile_sanctions(principal: OpExpr, _ctx: &CompileCtx) -> OpExpr {
    OpExpr::Call(
        "sanctions.check".to_string(),
        vec![("principal".to_string(), principal)],
    )
}
