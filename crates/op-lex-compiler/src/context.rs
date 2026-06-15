//! Compilation context — prelude, jurisdiction, gas budget.
//!
//! The admissible fragment restricts `Var` references to the prelude. The
//! prelude binding is therefore load-bearing: it enumerates the names the
//! compiler treats as free variables with known lowering rules. A variable
//! whose name is not in the prelude triggers
//! [`CompileError::UnboundVariable`](crate::error::CompileError::UnboundVariable).

use op_core::{Contracts, GasBudget, OpExpr, OpType};
use std::collections::BTreeMap;

/// Information the prelude carries about a named callable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreludeCallable {
    /// Op-level type (for downstream typechecking).
    pub ty: OpType,
    /// Lowering strategy.
    pub lower: PreludeLower,
}

/// How a prelude callable lowers into Op.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PreludeLower {
    /// Lower into an `OpExpr::BinOp(op, a, b)` with the given two-place
    /// reduction. Used for `equals`, `and`, `or`, `lt`.
    BinOp(op_core::BinOp),
    /// Lower into an `OpExpr::UnOp(op, x)`. Used for `not`, `neg`.
    UnOp(op_core::UnOp),
    /// Lower into an `OpExpr::Call(name, args)` — the callee is a
    /// host-recognized primitive with no native operator.
    PrimitiveCall {
        /// Primitive qualified name.
        name: String,
    },
    /// Lower into a literal expression computed at compile time from a
    /// constant argument list. Used for `true`, `false`, unit-valued
    /// constants.
    ConstantLiteral(OpExpr),
    /// Lower into a fixed expression, regardless of argument shape. Used for
    /// `prelude.contains` when the host exposes membership as `in`.
    FixedExpr(OpExpr),
}

/// Binding environment for prelude names and bound variables.
#[derive(Debug, Clone, Default)]
pub struct PreludeBinding {
    /// Named callables indexed by qualified name.
    callables: BTreeMap<String, PreludeCallable>,
    /// Named values (booleans, known entity references, jurisdiction codes)
    /// available as `Var`.
    values: BTreeMap<String, (OpType, OpExpr)>,
    /// Variant-type constructor sets. Used by the admissibility gate to
    /// decide match exhaustiveness.
    variant_constructors: BTreeMap<String, Vec<String>>,
}

impl PreludeBinding {
    /// Empty prelude.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Register a callable.
    pub fn add_callable(mut self, name: &str, ty: OpType, lower: PreludeLower) -> Self {
        self.callables
            .insert(name.to_string(), PreludeCallable { ty, lower });
        self
    }

    /// Register a value.
    pub fn add_value(mut self, name: &str, ty: OpType, expr: OpExpr) -> Self {
        self.values.insert(name.to_string(), (ty, expr));
        self
    }

    /// Register the constructor set of a variant type used as a scrutinee.
    pub fn add_variant(mut self, ty_name: &str, constructors: Vec<String>) -> Self {
        self.variant_constructors
            .insert(ty_name.to_string(), constructors);
        self
    }

    /// Lookup a callable.
    pub fn lookup_callable(&self, name: &str) -> Option<&PreludeCallable> {
        self.callables.get(name)
    }

    /// Lookup a value.
    pub fn lookup_value(&self, name: &str) -> Option<&(OpType, OpExpr)> {
        self.values.get(name)
    }

    /// Lookup the constructor set of a variant type.
    pub fn lookup_variant(&self, ty_name: &str) -> Option<&Vec<String>> {
        self.variant_constructors.get(ty_name)
    }

    /// Canonical prelude for the golden tests and example — carries the
    /// small set of primitives the admissible fragment needs:
    ///
    /// - `prelude.equals`, `prelude.and`, `prelude.or`, `prelude.not` — the
    ///   boolean algebra over first-order data.
    /// - `prelude.contains` — list membership.
    /// - `prelude.true`, `prelude.false`, `prelude.unit` — base literals.
    /// - `prelude.sanctions_check` — the host primitive for sanctions
    ///   screening. Emitted by `case_sanctions`.
    pub fn canonical() -> Self {
        use op_core::{BinOp, UnOp};
        Self::empty()
            .add_callable(
                "prelude.equals",
                OpType::Bool,
                PreludeLower::BinOp(BinOp::Eq),
            )
            .add_callable("prelude.and", OpType::Bool, PreludeLower::BinOp(BinOp::And))
            .add_callable("prelude.or", OpType::Bool, PreludeLower::BinOp(BinOp::Or))
            .add_callable("prelude.not", OpType::Bool, PreludeLower::UnOp(UnOp::Not))
            .add_callable("prelude.lt", OpType::Bool, PreludeLower::BinOp(BinOp::Lt))
            .add_callable(
                "prelude.contains",
                OpType::Bool,
                PreludeLower::BinOp(BinOp::Contains),
            )
            .add_callable(
                "prelude.sanctions_check",
                OpType::Variant(vec![
                    ("Compliant".to_string(), OpType::Unit),
                    ("SanctionsBlocked".to_string(), OpType::Unit),
                ]),
                PreludeLower::PrimitiveCall {
                    name: "sanctions.check".to_string(),
                },
            )
            .add_value("prelude.true", OpType::Bool, OpExpr::Bool(true))
            .add_value("prelude.false", OpType::Bool, OpExpr::Bool(false))
            .add_value("prelude.unit", OpType::Unit, OpExpr::Unit)
            .add_variant(
                "Verdict",
                vec![
                    "Compliant".to_string(),
                    "NonCompliant".to_string(),
                    "SanctionsBlocked".to_string(),
                ],
            )
    }
}

/// Jurisdiction label — a minimal newtype matching Op's ambient-jurisdiction
/// slot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Jurisdiction(pub String);

impl Jurisdiction {
    /// Generic jurisdiction used when the program is jurisdictionally agnostic.
    pub fn default_() -> Self {
        Jurisdiction("_default".to_string())
    }
}

/// Compilation context carried through the case functions.
///
/// `lex_contracts` carries the program's declared Lex-rule contracts (proposal
/// §2.1/§5) in the canonical fully-explicit form (proposal §4.1): the host
/// supplies the `Contract::LexRule` declarations and `build_program` emits
/// them, after which the op-core type checker structurally discharges each
/// (§3.2). The `Contract::LexRule` AST variant now exists in op-core, so the
/// fully-explicit path is real and exercised.
///
/// FOLLOW-ON (proposal §5 *pack-driven* population): `CompileCtx` still carries
/// NO active-pack handle, so the compiler does not yet resolve
/// `pack.rules_for(jurisdiction, operation_type)` to *derive* the contracts
/// from a pack (it emits what the host explicitly supplies in `lex_contracts`).
/// Pack-driven population — and the §3.1 completeness check it feeds — depends
/// on the `lex-pack` crate (`Pack`, `CompiledLexPredicate`, `Pack::rules_for`),
/// which does not exist yet (companion `~/lex/docs/frontier-work/09` §3,
/// design-only). `auto_lex` is sugar over the explicit form (proposal §4.2);
/// the canonical program is always fully explicit, which is what `lex_contracts`
/// holds.
#[derive(Debug, Clone)]
pub struct CompileCtx {
    /// Prelude binding.
    pub prelude: PreludeBinding,
    /// Ambient jurisdiction.
    pub jurisdiction: Jurisdiction,
    /// Gas budget to attach to the emitted program.
    pub gas_budget: GasBudget,
    /// Explicitly-declared Lex-rule contracts to attach to the emitted program
    /// (proposal §2.1/§4.1 fully-explicit form). Empty by default — a program
    /// with no declared rules emits `Contracts::default()` exactly as before.
    pub lex_contracts: Contracts,
    /// Program name for the emitted program.
    pub program_name: String,
    /// Branch-scoped binders: constructor payload bindings introduced by
    /// pattern matches, threaded through the branch body so the compiler's
    /// downstream cases (type inference, admissibility, prelude lookup)
    /// see the constructor-local names.
    ///
    /// The admissible fragment today uses nullary constructors — the map
    /// is vacuous in practice. When dependent match becomes admissible,
    /// each match arm will push its binder here before compiling the
    /// arm body, and pop it when the body finishes.
    pub binders: BTreeMap<String, OpType>,
}

impl CompileCtx {
    /// Construct a context with the canonical prelude and default jurisdiction.
    pub fn with_canonical_prelude(program_name: &str) -> Self {
        Self {
            prelude: PreludeBinding::canonical(),
            jurisdiction: Jurisdiction::default_(),
            gas_budget: GasBudget::default(),
            lex_contracts: Contracts::default(),
            program_name: program_name.to_string(),
            binders: BTreeMap::new(),
        }
    }

    /// Attach explicitly-declared Lex-rule contracts to be emitted on the
    /// program (proposal §2.1/§4.1 fully-explicit form). The op-core type
    /// checker structurally discharges each (§3.2) when the emitted program is
    /// type-checked in `compile_lex`.
    pub fn with_lex_contracts(mut self, contracts: Contracts) -> Self {
        self.lex_contracts = contracts;
        self
    }

    /// Extend the context with constructor-payload binders for a match arm.
    ///
    /// The returned `CompileCtx` owns a fresh binder map that shadows the
    /// parent's bindings for the duration of the arm body's compilation.
    /// Callers should compile the arm body against the returned value and
    /// discard it — binders do NOT escape the arm.
    pub fn with_binders(&self, new_binders: Vec<(String, OpType)>) -> Self {
        let mut extended = self.clone();
        for (name, ty) in new_binders {
            extended.binders.insert(name, ty);
        }
        extended
    }

    /// Look up a binder introduced by an enclosing match arm.
    pub fn lookup_binder(&self, name: &str) -> Option<&OpType> {
        self.binders.get(name)
    }
}
