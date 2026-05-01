# Proposal: `Contract::LexRule` and Pack-Driven Discharge Completeness

This proposal extends Op's contract surface so that a program can declare
which Lex rules it discharges, and so that the type checker can
mechanically reject any program whose declared discharges do not cover
the set of rules a curator pack binds to the program's
`(operation_type, jurisdiction)`. The extension is small at the AST
level, structural at the type-checker level, and load-bearing for the
Lex→Op binding the canonical languages have so far left as prose.

Companion proposal:
`~/lex/docs/frontier-work/09-rule-applies-to-and-pack-binding.md`
(extends `DefeasibleRule` with `applies_to`; specifies the pack format
this proposal consumes; the two proposals must land together).

This is a frontier design note, not a canonical language reference.
Status doctrine (per `AGENTS.md`/`CLAUDE.md`): everything in this
document is **proposed**; implementation lands as a sequence of PRs each
of which promotes one line above frontier status only after the
corresponding type-checker rule, formal scaffold, and worked example
are in place.

## 1. Motivation

Op already keys every program by `(operation_type, jurisdiction)`
(`docs/language-spec.md` §2). Op already exposes the contract clauses
the rule layer hands to the workflow layer:

```op
requires domains [...];
ensures domains [...];
```

`docs/language-spec.md` line 36 names them: "Contract clauses consumed
by the rule layer." The infrastructure to consume rule-layer artifacts
already exists: `Contracts { requires, ensures }` is a top-level block
on every `OpProgram` (`crates/op-core/src/ast.rs:22-48`), and
`op-lex-compiler` has a place to put compiled rules
(`crates/op-lex-compiler/src/lib.rs:315`).

What is missing: the compiler currently produces `Contracts::default()`.
Every Op program ships with empty contracts. This is not a Lex bug — it
is a binding bug. There is no typed reference Op can put inside
`Contracts::requires` that names a specific Lex rule, no completeness
check that asks "is the program's set of declared rules sufficient for
its `(operation_type, jurisdiction)` under the active pack?", and no
mechanical discharge check that verifies the program's steps satisfy
the rule's compiled predicate.

The companion Lex proposal supplies one half: rules now declare typed
`applies_to: { jurisdictions, operation_kinds }`, and a pack bundles
the resulting `CompiledLexPredicate` artifacts. This proposal supplies
the other half.

## 2. The `Contract::LexRule` variant

### 2.1 AST extension

`crates/op-core/src/ast.rs` defines `Contract` (today's variants):

```rust
pub enum Contract {
    Domains(Vec<String>),
    Expr(OpExpr),
}
```

Add one variant:

```rust
pub enum Contract {
    Domains(Vec<String>),
    Expr(OpExpr),
    /// References a Lex rule supplied by the active pack. The type
    /// checker resolves the reference at program-compile time, fetches
    /// the rule's `CompiledLexPredicate` body from the pack, and
    /// verifies the program's steps structurally discharge it. The
    /// Lex evaluator is NEVER re-executed at the Op boundary.
    LexRule(LexRuleRef),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexRuleRef {
    /// Content hash of the rule, as carried in the pack.
    pub rule_hash: LexRuleHash,
    /// Declared jurisdiction. MUST match the program's
    /// `OpProgram.jurisdiction` exactly, OR be a wildcard explicitly
    /// covered by the rule's `applies_to` declaration.
    pub jurisdiction: QualIdent,
    /// Pinned pack version. The type checker rejects programs whose
    /// declared pack version does not match the active pack at compile
    /// time. This is the deterministic-replay binding.
    pub pack_version: PackVersion,
}
```

### 2.2 Surface syntax

```op
op entity.incorporate for sc
requires lex {
  rule rule_hash:b3:0xa1c2... in pack curator:sc-dict@v1.4.0;
  rule rule_hash:b3:0x7f8e... in pack curator:sc-dict@v1.4.0;
}
ensures lex {
  rule rule_hash:b3:0x9d31... in pack curator:sc-dict@v1.4.0;
}
do {
  step gate : EntityId -> Bool ! {sanctions_check} ...;
  step register : ... ! {sovereign_write} ...;
}
```

`requires lex { ... }` is sugar over `requires` with `Contract::LexRule`
elements. The hashes are content-addressed (BLAKE3 in canonical
encoding); the pack reference is `curator:DID@semver`. Surface syntax
is parser-only; the AST stays canonical.

For everyday authoring, the expectation is not that humans write rule
hashes by hand. The expectation is that Op authors write the program's
operation/jurisdiction header and let `op-lex-compiler` populate the
contract block from the active pack. The surface syntax is for
generated programs and explicit, audited declarations. See §4 on
authoring discipline.

## 3. Type-checker rule: completeness and discharge

Two new checks. Both are structural, fail-closed, and fire at
`crates/op-core/src/types.rs::typecheck_program`.

### 3.1 Completeness against the active pack

```
For every Op program P with declared (operation_type, jurisdiction):
  let required_rules = active_pack.rules_for(P.jurisdiction, P.operation_type)
  let declared_rules = { ref.rule_hash | C::LexRule(ref) ∈ P.contracts.requires }
  if declared_rules ⊉ { r.rule_hash | r ∈ required_rules }
    then reject TypeError::IncompleteLexDischarge {
      operation: P.operation_type,
      jurisdiction: P.jurisdiction,
      missing: required_rules \ declared_rules,
    }
```

Plain English. The Op type checker queries the pack for every Lex rule
whose `applies_to` matches the program. The program must declare each
of those rules in its `requires` block (the rule is one the program
must satisfy). If the program's declared set omits a rule the pack
binds, the program does not type-check.

This is the gate that closes the "operation YAML/program is silently
non-compliant" failure mode the kernel currently has at boot. After
this rule, an Op program that does not name every required Lex rule
for its jurisdiction is rejected before it can be admitted to any
host.

### 3.2 Structural discharge per rule

For each `Contract::LexRule(ref)` in `requires`:

```
let predicate = active_pack.lookup(ref.rule_hash)
  .ok_or(TypeError::UnknownLexRule { hash: ref.rule_hash })?

if predicate.pack_version != ref.pack_version
  then reject TypeError::PackVersionMismatch { ... }

structural_discharge(P.body, predicate)?
```

`structural_discharge` is a syntactic check, not a runtime evaluation.
It walks the program body and verifies a structural witness exists for
the rule's compiled predicate. The exact rules:

- A predicate of shape `requires sanctions_check on subject S` is
  discharged if the program contains a step with `sanctions_check`
  in its effect row whose input includes `S`.
- A predicate of shape `requires governance_request on policy P` is
  discharged if the program contains a step with `governance_request`
  effect bound to `P`.
- A predicate of shape `requires obligation O before write` is
  discharged if every write-class effect (`sovereign_write`,
  `identity_mutation`, `fiscal_transfer`) in the program is dominated
  in the effect-DAG by a step that emits the obligation `O`.
- A predicate of shape `ensures certificate C` is discharged if the
  program emits `C` as a `proof_emit` effect on some step before
  termination.

This list is not exhaustive. The full grammar of structural-discharge
patterns is the contract `lex-core` + `op-stdlib` + `op-core` agree on
in `~/lex/docs/frontier-work/09` §3.2's `CompiledTerm`. New patterns
are added by joint PR; neither language adds patterns unilaterally.

The Lex evaluator is **never** re-run at the Op compile boundary.
`structural_discharge` is decidable in time linear in the size of the
program plus the size of the predicate body; no SMT, no fixpoint.

### 3.3 Sanctions terminal: I-1 enforcement at the type checker

Every pack must contain a sanctions-terminal rule (the universal
`applies_to { *, * }` rule from the companion proposal §2.3). The Op
type checker verifies that every program declares this rule in its
`requires`. The rule's predicate is:

```
NonCompliant(reason = "sanctions") ⇒ reject_admission
```

The corresponding `structural_discharge` pattern: the program must
contain a `sanctions_check` step that gates every write-class effect.
This is exactly the existing Op effect-safety rule (`types.rs:198`).
The Lex-rule layer adds: the rule is named, content-addressed, and
the program declares it explicitly. I-1 is enforced twice — once
structurally by Op's effect rules, once by `structural_discharge`
against the sanctions-terminal Lex rule. Defense in depth at the type
checker.

## 4. Authoring discipline

The surface syntax in §2.2 is fully explicit and intended to be
machine-generated for production use. Three authoring paths:

### 4.1 Hand-written explicit declarations

For audit-grade or regulator-facing operations, the author writes the
rule hashes and pack version explicitly. The hashes are in the program
source; the program's identity (its content hash) commits to the pack
version it was compiled against. Replay is exact.

### 4.2 Compiler-driven population

For everyday authoring, the author writes the program's
`(operation_type, jurisdiction)` header and an `auto_lex` annotation:

```op
op entity.incorporate for sc
auto_lex pack curator:sc-dict@v1.4.0
do { ... }
```

`op-lex-compiler` queries the named pack, resolves
`pack.rules_for(sc, entity.incorporate)`, generates explicit
`Contract::LexRule` entries for every required rule, and emits the
fully explicit program. The fully explicit form is what gets
type-checked, hashed, and shipped. `auto_lex` is sugar; the canonical
program is always fully explicit.

### 4.3 YAML lowering (kernel-side, demolition scaffolding)

The kernel's existing YAML operation files are lowered to Op via
`mez-op-compiler`. After this proposal lands and the kernel adopts the
canonical Op surface, every YAML lowering produces a fully explicit
Op program with `Contract::LexRule` entries populated from the active
pack. YAML authors do not write `applies_to` and do not write rule
hashes; the lowering pipeline does it. YAML remains a kernel-side
authoring affordance, not a canonical Op surface.

## 5. Op-Lex-Compiler: from `Contracts::default()` to populated contracts

`crates/op-lex-compiler/src/lib.rs:315` today produces empty contracts.
After this proposal:

```rust
fn build_program(/* ... */) -> Result<Program, CompileError> {
    let pack = active_pack();
    let required = pack.rules_for(&jurisdiction, &operation_type);

    let requires_clauses = required
        .iter()
        .map(|p| Contract::LexRule(LexRuleRef {
            rule_hash: p.rule_hash.clone(),
            jurisdiction: jurisdiction.clone(),
            pack_version: pack.version.clone(),
        }))
        .collect();

    let ensures_clauses = /* analogous, derived from pack rule
                              metadata that distinguishes pre/post
                              obligations; see companion §3.3 */;

    Ok(Program {
        // ...
        contracts: Contracts {
            requires: requires_clauses,
            ensures: ensures_clauses,
        },
        // ...
    })
}
```

The `op-lex-compiler` is the canonical implementation of "given an
operation kind and a jurisdiction and a pack, what Lex rules apply".
Other Op hosts may implement their own (kernels, regulators, audit
tools), but the canonical implementation lives here.

## 6. Pack consumption protocol

Op programs do not embed packs. They reference them by version. The
host supplies the pack at compile time. Three boundaries:

1. **Build-time host.** When `op-lex-compiler` produces a program, it
   captures `pack.version` into every `LexRuleRef`. The program is
   replayable against the pack snapshot at the version it was built
   under.
2. **Validation host.** Any party verifying a program (regulator,
   auditor, peer kernel) can re-run the type checker by supplying the
   same pack version. Pack content-addressing makes this exact.
3. **Execution host.** A sovereign kernel admits a program only if its
   active pack is `>=` the program's `LexRuleRef.pack_version`. Forward
   compatibility (newer pack, older program) is allowed if the newer
   pack's `applies_to` set is a superset; backward compatibility
   (older pack, newer program) is rejected.

Pack discovery, signature verification, and pinning are host concerns,
not Op-language concerns. Op specifies only the reference shape and
the type-checker contract.

## 7. Effect-row interaction

`Contract::LexRule` does not introduce a new `Effect`. The rule's
predicate may demand effects (e.g. `sanctions_check`,
`governance_request`); those effects appear in the program's existing
effect row by virtue of the steps that discharge them. The Lex rule
layer is consumed by the contract layer, not by the effect layer.
This preserves the language-spec.md §1 statement: "Op makes these
language features instead of string conventions" — Lex obligations
become typed contract clauses, not new effects.

## 8. Compatibility and migration

### 8.1 Programs without `Contract::LexRule`

Existing Op programs that compile under the current language without
referencing any Lex rule are still well-typed under this proposal,
but only if the active pack's `rules_for(j, k)` set is empty for that
program's `(j, k)`. As soon as a pack binds any rule to that program's
`(j, k)`, the program fails completeness.

This is the migration path: pack curators introduce rules at known
deadlines; programs that target those `(j, k)` pairs must be recompiled
with explicit declarations before the deadline. The type checker
makes the failure mechanical.

### 8.2 Programs without an active pack

Op programs do not require a pack to type-check the rest of the
language (linearity, effect safety, type unification). They require a
pack only to type-check `Contract::LexRule` clauses. A program with
no `Contract::LexRule` and no pack still type-checks; a program with
`Contract::LexRule` and no pack fails with
`TypeError::NoActivePack`.

This means Op remains usable in pack-free contexts (testing, examples,
documentation), and acquires Lex-driven discharge whenever a pack is
supplied.

## 9. Formal scaffold updates

Per Op's status doctrine (`SUPREMUM.md` §2, language-spec EBNF
discipline):

- **Coq.** `formal/coq/Op/AST.v` adds `Contract::LexRule` and
  `LexRuleRef`. `formal/coq/Op/Typing.v` adds the
  `IncompleteLexDischarge` and `structural_discharge` rules.
  `progress` is preserved (the new rule is a check, not a reduction).
- **Lean.** `formal/lean/Op/AST.lean` and `Typing.lean` mirror.
- **Joint Lex/Op theorem.** `formal/coq/Joint/Discharge.v` proves
  `lex_discharge_soundness`: for any pack `P`, program `Q`, and rule
  `r ∈ P.rules_for(Q.j, Q.k)`, if Op's type checker accepts `Q` and
  `Q.requires ∋ Contract::LexRule(rule_hash = r.hash, ...)` and
  `structural_discharge(Q.body, P.lookup(r.hash).body)` succeeds, then
  every execution of `Q` against any entity state produces a Lex
  certificate that admissibly discharges `r`. This is the proof of
  the binding's soundness; without it, `Contract::LexRule` is just a
  data shape.

The joint theorem is the fence-post. Until it is proved, the
`Contract::LexRule` extension is admitted as scaffold; the production
mode is "type checker rejects under-declaration but host re-runs Lex
evaluator on the predicate body for cross-validation". Once the
joint theorem is closed, the host re-execution can be removed and
the type checker becomes load-bearing.

## 10. Open obligations

1. **Joint sourcing of `OperationKind`.** The companion Lex proposal
   defers to `op-stdlib` for the canonical operation-kind list. This
   proposal must specify:
   - `op_stdlib::canonical::CANONICAL_PRIMITIVES` (the existing
     `&'static [PrimitiveShape]` slice in
     `crates/op-stdlib/src/canonical.rs`) is the source of truth;
     `op_stdlib::canonical::lookup(name)` is the canonical resolver.
   - A change to that slice is a coordinated `op-stdlib` + `lex-pack`
     update; old packs whose `applies_to` references a since-removed
     primitive are rejected at pack-load with
     `PackLoadError::UnknownOperationKind`.
2. **Pack signature scheme.** The companion proposal specifies hybrid
   PQ. This proposal must specify the exact verification interface
   (`pack.verify_signature(curator_did) -> Result<()>`) and the
   `mez-trust`-equivalent verifier. Op should not depend on the
   kernel's `mez-trust`; the canonical verifier lives in a new
   `op-pack-verify` crate or, preferably, in `lex-pack` itself
   alongside the pack format definition.
3. **`structural_discharge` pattern grammar.** §3.2 lists four
   patterns. The full grammar is a joint Lex/Op artifact and lives
   in `~/lex/docs/frontier-work/09` §6.3 (to be added in v2 of that
   doc). Until that grammar stabilizes, the type checker accepts a
   conservative subset and the host re-runs the Lex evaluator on the
   predicate body for any pattern not in the subset. This is
   demolition scaffolding: it has a deadline, an owner, and a
   sunset.
4. **Multi-pack composition.** A host may layer multiple packs (a
   federal pack, a ministerial pack, an industry-vertical pack). The
   completeness check (§3.1) takes the union of all their
   `rules_for` sets. The exact semantics of multi-pack precedence
   (lattice meet on verdict at runtime; structural discharge per
   rule at compile time; conflict resolution between two rules
   binding the same `(j, k)` with incompatible structural patterns)
   is open and named in the companion proposal §6.4.

## 11. What this changes about the canonical languages

The Lex paper says: "Op steps reference proof obligations through
`requires` and `ensures` contracts." This proposal makes that
reference typed and content-addressed. The reference becomes
verifiable at compile time without re-executing the Lex evaluator
and without involving the host.

The Op paper says: "Op is the workflow layer; Lex is the rule layer;
neither redefines the other's semantics." This proposal does not
redefine either. Op consumes a frozen Lex artifact (the
`CompiledLexPredicate` body) the same way it consumes any other
contract clause: as data the type checker reads, not as code the
type checker runs.

What this proposal does change: the binding between the two
languages, which today is prose, becomes a typed pack-mediated
contract. Authoring binding becomes mechanical (compiler-driven from
the pack); audit becomes mechanical (rule hashes are in the program
source); replay becomes exact (pack version is pinned per
reference). The kernel-private adapter pattern goes away because
there is nothing kernel-private left to write.

## 12. Status

Frontier proposal. Awaits:

- Coordinated landing with companion Lex proposal.
- `lex-pack` crate (proposed in companion §3.1).
- `op-stdlib::canonical::primitives()` exported as the canonical
  operation-kind source.
- `formal/coq/Joint/Discharge.v` `lex_discharge_soundness` theorem.
- A worked example: `~/op/examples/sc-incorporate-with-lex.rs` shows
  the full pipeline end-to-end using a small example pack.

No production host should adopt this surface before all five land.
