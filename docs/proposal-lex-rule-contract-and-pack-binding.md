# Proposal: `Contract::LexRule` and Pack-Driven Discharge Completeness

Status: proposal. This document describes a public language extension for Op.
It is not the canonical language reference until the AST, type checker, formal
scaffolds, and examples named below land in this repository.

This proposal gives Op a typed way to say which Lex rules a program discharges.
It also gives the Op type checker a mechanical completeness rule: a program
whose declared Lex-rule discharges do not cover the rules required by the
active pack for `(operation_type, jurisdiction)` is rejected before admission.

The companion Lex work is public and belongs in the Lex repository. It extends
Lex rules with typed `applies_to` metadata and defines the pack artifact shape
that Op consumes here.

## 1. Motivation

Op already keys every program by `(operation_type, jurisdiction)`.
Op already has precondition and postcondition contract clauses:

```op
requires domains [...];
ensures domains [...];
```

The language also already has a `Contracts` block on each program. What is
missing is a typed reference that names a specific Lex rule, a completeness
check that asks whether the program covers all rules required by an active
pack, and a structural discharge check that verifies the program body witnesses
each declared rule.

Without this binding, a workflow can compile with an empty contract set even
when a jurisdictional rule pack would require rule-level evidence. That is a
language binding gap, not a host integration detail.

## 2. `Contract::LexRule`

Extend the public contract enum with one variant:

```rust
pub enum Contract {
    Domains(Vec<String>),
    Expr(OpExpr),
    LexRule(LexRuleRef),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexRuleRef {
    pub rule_hash: LexRuleHash,
    pub jurisdiction: QualIdent,
    pub pack_version: PackVersion,
}
```

Semantics:

- `rule_hash` is the content hash of the Lex rule artifact in the pack.
- `jurisdiction` must match `OpProgram.jurisdiction`, unless the Lex rule's
  `applies_to` metadata explicitly covers a wildcard jurisdiction.
- `pack_version` pins the pack snapshot used to compile the program.

The Op compiler resolves `LexRuleRef` values at program-check time. It fetches
the corresponding compiled predicate from the active pack and verifies that
the program structurally discharges it. The Lex evaluator is not re-executed
inside the Op type checker.

## 3. Surface Syntax

One possible surface form:

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

`requires lex { ... }` is syntax sugar over `Contract::LexRule` entries. The
canonical AST remains explicit. Humans do not need to author rule hashes by
hand in ordinary use; compiler-driven population from a named pack is the
default path.

## 4. Completeness Against The Active Pack

For every Op program `P`:

```text
required_rules = active_pack.rules_for(P.jurisdiction, P.operation_type)
declared_rules = { ref.rule_hash | Contract::LexRule(ref) in P.contracts.requires }

if declared_rules is not a superset of required_rules.hashes:
    reject IncompleteLexDischarge { operation, jurisdiction, missing }
```

Plainly: the pack determines which Lex rules apply to the program's operation
kind and jurisdiction. The program must declare every required rule. Missing a
rule is a type error.

This is fail-closed. A host cannot accidentally admit a program that omits a
rule required by the pack it is compiling against.

## 5. Structural Discharge

For each declared `Contract::LexRule(ref)`:

```text
predicate = active_pack.lookup(ref.rule_hash)
if predicate is missing:
    reject UnknownLexRule
if predicate.pack_version != ref.pack_version:
    reject PackVersionMismatch
structural_discharge(P.body, predicate)
```

`structural_discharge` is syntactic. It walks the program and checks that a
structural witness exists for the compiled predicate. It does not call an SMT
solver and does not evaluate Lex at runtime.

Initial predicate patterns:

- `requires sanctions_check on subject S` is discharged by a step whose effect
  row contains `sanctions_check` and whose input includes `S`.
- `requires governance_request on policy P` is discharged by a step with
  `governance_request` bound to `P`.
- `requires obligation O before write` is discharged when every write-class
  effect is dominated in the effect DAG by a step that emits obligation `O`.
- `ensures certificate C` is discharged when a step emits `C` through
  `proof_emit` before termination.

The complete pattern grammar is a joint Lex/Op public artifact. New patterns
require coordinated changes to Lex pack construction, Op structural discharge,
formal statements, and examples.

## 6. Authoring Paths

### 6.1 Explicit Declarations

An audit-grade program may include every rule hash and pack version directly
in source. The program's content hash then commits to the rule set and pack
snapshot it was compiled against.

### 6.2 Compiler-Driven Population

For ordinary authoring, the source can name the pack:

```op
op entity.incorporate for sc
auto_lex pack curator:sc-dict@v1.4.0
do { ... }
```

The compiler expands this into explicit `Contract::LexRule` entries by calling
`pack.rules_for(jurisdiction, operation_type)`. The expanded program is what
gets type-checked, hashed, and distributed.

### 6.3 External Lowering

External authoring formats can lower into the same explicit AST. The lowering
pipeline is responsible for resolving the active pack and emitting the same
`Contract::LexRule` entries the native Op compiler would emit. Such formats
are authoring conveniences; the canonical program is the fully explicit Op
program.

## 7. Pack Consumption Protocol

Op programs do not embed packs. They reference pack versions.

1. **Build-time host.** The compiler captures `pack_version` in every
   `LexRuleRef`.
2. **Validation host.** A verifier can re-run the type checker with the same
   pack snapshot.
3. **Execution host.** A host admits the program only when it can supply the
   referenced pack snapshot or a compatible newer pack whose `applies_to` set
   is a conservative superset.

Pack discovery, signature verification, trust policy, and pinning are host
concerns. Op specifies the reference shape and type-checker contract.

## 8. Effect Rows

`Contract::LexRule` does not add a new effect. A Lex predicate may demand
effects such as `sanctions_check` or `governance_request`; those effects still
appear in the ordinary Op effect row on the steps that discharge them.

The rule layer is consumed by contracts, not by redefining the effect system.

## 9. Compatibility

Existing Op programs without `Contract::LexRule` remain valid when no active
pack binds rules to their `(jurisdiction, operation_type)` pair. Once a pack
does bind rules to that pair, the program must be recompiled with explicit
Lex-rule declarations.

Programs can still type-check without any active pack if they contain no
`Contract::LexRule` clauses. A program that contains `Contract::LexRule`
clauses and is checked without a pack fails with `TypeError::NoActivePack`.

## 10. Formal Obligations

Before this proposal becomes canonical:

- Coq AST and typing definitions include `Contract::LexRule` and
  `LexRuleRef`.
- Lean mirrors the AST and typing additions.
- The type checker implements `IncompleteLexDischarge`,
  `UnknownLexRule`, `PackVersionMismatch`, and `NoActivePack`.
- A joint Lex/Op theorem states that if Op accepts a program and
  `structural_discharge` succeeds for each required rule, then every accepted
  execution produces evidence sufficient to discharge those Lex rules under
  the referenced pack snapshot.
- A worked example demonstrates pack-driven compilation end to end using a
  small public example pack.

Until the joint theorem and implementation land, hosts that need production
assurance should treat this surface as scaffold: reject under-declaration in
the type checker, and independently validate compiled predicates at the host
boundary.

## 11. Open Design Items

1. **Canonical operation-kind source.** The operation-kind list should be
   resolved through `op_stdlib::canonical` so Lex packs and Op programs share
   one public vocabulary.
2. **Pack signature interface.** The public pack verifier should expose a
   stable interface, for example
   `pack.verify_signature(curator_did) -> Result<()>`.
3. **Structural-discharge grammar.** The initial four patterns above are a
   conservative subset. The full grammar must be jointly specified and tested.
4. **Multi-pack composition.** A host may layer several packs. Completeness is
   the union of `rules_for` sets; precedence and conflict handling between
   incompatible structural patterns remains open.

## 12. Result

The Lex/Op binding becomes typed and content-addressed. Authoring becomes
mechanical, audit becomes rule-hash based, replay becomes pack-version exact,
and hosts no longer need host-specific adapters to explain which rule
obligations a program claims to discharge.
