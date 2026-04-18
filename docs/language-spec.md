# Op Language Reference

## 1. What Op Is

Op is a typed effectful workflow language for multi-step economic programs.
A program names its inputs and outputs, composes a DAG of typed steps, and
declares the operational effects those steps impose on sovereign state. A
host fulfills the primitive calls. The language carries the scaffolding:
parsing, typing, effect safety, gas accounting, and deterministic replay.

**The promise.** A program that type-checks composes correctly, accounts
for its effects, preserves its compensation scope, and lowers
deterministically to an execution plan. Same program + same inputs + same
host → same trace on every replay.

**What it replaces.** Workflow definitions encoded in YAML or JSON carry
language semantics — step composition through `depends_on` edges, variable
binding through string-path interpolation, control flow through embedded
expression fragments, suspension through callback tokens, failure policy
through ad hoc enumerations, compensation detached from the step it
inverts. Op makes these language features instead of string conventions.

### Instruction set at a glance

| Surface | What it is |
|---|---|
| `step name : In -> Out ! E { body }` | Smallest named unit; typed input, output, and effect row. |
| `a ; b` | Sequential composition; later steps see earlier bindings. |
| `par { a = e1; b = e2; }` | Parallel branches; no sibling data-dependence. |
| `choose { when cond -> ... else -> ... }` | Guarded choice; all arms unify to a common output. |
| `await e within d` | Typed callback suspension; the step's result is `Await<e, T>`. |
| `compensate { ... }` | Inverse branch attached to the forward step. |
| `in jurisdiction { ... }` | Ambient-jurisdiction rebind inside a scope. |
| `policy name using backend { prove domains [...] }` | SAVM-style proof block; the host backs the verifier. |
| `requires domains [...]; ensures domains [...];` | Contract clauses consumed by the rule layer. |

Nine tracked effects — `sovereign_write`, `identity_mutation`,
`fiscal_transfer`, `sanctions_check`, `governance_request`,
`document_generation`, `external_read`, `proof_emit`,
`await <event>` — compose by union. Any reachable write-class effect
(`sovereign_write`, `identity_mutation`, `fiscal_transfer`) must be
dominated by a `sanctions_check`, with one narrow deferred-subject
exception for entity creation.

### A two-line example

```op
op entity.activate for _default
do {
  step gate : EntityId -> Bool ! {sanctions_check}
    screening.sanctions({ subject_id: entity_id });
  step activate : { entity_id: EntityId } -> { status: String } ! {sovereign_write}
    update.entity_status({ entity_id: entity_id, status: "ACTIVE" });
}
```

The `gate` step carries `sanctions_check`; it dominates the downstream
`activate` write. Remove the gate and the type checker rejects the
program before any primitive runs.

### What comes next in this document

Sections 2–13 are the full reference: core concepts, the type system,
the effect system, contracts, compensation, multi-entity operations,
jurisdiction resolution, the two-tier gas model, policy blocks, the
host ABI, the EBNF grammar, and worked examples.

### Getting started hands-on

The fastest way to see Op run: `cargo run --example hello-op -p op-core`
from a fresh clone. A cold-reader five-minute walk-through lives at
`docs/getting-started.md`.

---

## 2. Core Concepts

An Op program denotes one executable operation family. Its canonical
identity is the pair `(operation_type, jurisdiction)` — the same pair used
by the lowered execution plan.

The semantic core has four objects: **steps**, **primitives**,
**compensation**, and **composition**.

- A **step** is the smallest named unit that consumes input, produces output,
  declares effects, may suspend on a callback, declares a failure policy, and
  may expose an inverse branch. Each step has a signature
  `In -> Out ! Effects`.
- A **primitive** is a host-recognized action with stable lowering rules.
  Examples include entity creation, fiscal transfer, sanctions screening,
  document generation, registry filings, governance ceremonies. Primitives
  are given no built-in semantics by Op; the host supplies interpretations
  through the `OpHost` trait.
- **Compensation** is a typed inverse program over committed side effects.
  It is local to the step it inverts; the compiler derives a
  reverse-topological rollback plan from the forward DAG.
- **Composition** is how steps form a workflow. The minimum compositional
  operators are sequential `a ; b`, parallel `par { ... }`, guarded choice
  `choose { ... }`, callback suspension `await e within d`, and scoped
  compensation `compensate { ... }`.

A program runs in a typed environment: program parameters, completed step
outputs, ambient jurisdiction, time-derived extras, and caller identity. The
important change relative to string-interpolated workflow configuration is
that bindings become typed names instead of string paths.

## 3. Type System

Op is statically typed. The typing judgment is

```
Gamma |- e : T ! E
```

where `Gamma` is the environment, `T` is the result type, and `E` is the
effect row.

**Base types.** The language recognizes host-native domain types rather than
collapsing everything into untyped JSON:

- `Unit`, `Bool`, `Int`, `String`
- `Date`, `Timestamp`, `Duration`
- `EntityRef`, `JurisdictionRef`, `MoneyAmount`, `ContentDigest`,
  `CallbackEvent`

The opaque types are interpreted by the host. A host implementation fixes
the interpretation of `EntityRef` (identifier vocabulary), `MoneyAmount`
(currency and minor-unit semantics), and `ContentDigest` (hash algorithm).

**Structural types.** Op includes records, variants (tagged unions), lists,
optionals, tuples, and a `Result<T, E>` binary. Records are structural; named
aliases are permitted for readability and public API stability.

**Linear and locked resources.** Two specialized type constructors model
single-use resources and three-phase-commit locks:

- `Linear<T>` — the resource may be consumed at most once. A program that
  consumes a linear resource twice fails to type-check.
- `Locked<T>` — the resource is in a locked state with exactly two
  eliminators: `commit_transfer(witness_foreign_minted)` which consumes, and
  `release_lock(witness_foreign_aborted)` which restores the resource to
  `Linear<T>`.

**Await types.** A waiting step returns `Await<Event, Payload>`. Waiting is
operationally distinct from completion, and the type system reflects that:
a downstream step that treats an `Await<E, P>` as if it were `P` fails to
type-check.

**Step signatures.** Every step declares an explicit signature:

```
step name : In -> Out ! Effects
```

**Composition operators.**

| Operator | Meaning |
|---|---|
| `a ; b` | Sequential composition. Later steps see earlier bindings. |
| `par { ... }` | Sibling branches; no sibling data-dependence. |
| `choose { ... }` | Guarded choice; all arms unify to a common output type. |
| `await e within d` | Callback boundary; carries typed `Await<e, _>`. |
| `compensate { ... }` | Inverse branch attached to the forward step. |

**Binding and projection.** String-path interpolation is replaced by ordinary
binding and projection. Instead of a workflow-config idiom such as
`"{steps.entity_create.result.id}"`, Op writes:

```
let entity_id: EntityRef = entity_create.id;
```

String interpolation survives as `"${name}"` inside literal strings, but it
occurs after typing — the referenced bindings must exist and have resolvable
types.

## 4. Effect System

Type safety is necessary but not sufficient. A program can be type-correct
and still operationally unsafe. Op therefore tracks effects.

Tracked effects:

- `sovereign_write` — mutates sovereign-owned state.
- `identity_mutation` — modifies identity state.
- `fiscal_transfer` — moves or commits value.
- `sanctions_check` — mandatory gate before write-class effects.
- `governance_request` — initiates a governance ceremony.
- `document_generation` — produces a document artifact.
- `external_read` — reads external state.
- `proof_emit` — emits proof obligations / attestations.
- `await <event>` — suspends on a callback event.

**Effect rows compose by union.** Certain effect pairs impose ordering
constraints.

**Safety rule.** A reachable `sovereign_write`, `identity_mutation`, or
`fiscal_transfer` must be dominated by a `sanctions_check`, with one
deferred-subject exception: entity creation, where the subject does not
yet exist at the time of the check. Hosts that run post-flight evaluation
against the created entity satisfy the rule.

The compiler rejects programs that:

1. have a reachable write-class branch with no dominating sanctions check
   (outside the deferred-subject case),
2. perform a `fiscal_transfer` without a typed monetary value,
3. attach a compensation branch to a step with no compensable effect,
4. declare a `continue` failure path on a step carrying `sovereign_write`
   (which would silently bury a failed mutation).

**Effect inference.** Default effect rows are inferred from primitive
families. A host may override the defaults for its embedding.

## 5. Contracts

A step or program may declare preconditions (`requires`) and postconditions
(`ensures`). Contracts are attached to the program or step and are discharged
by the host at runtime (for domain-shorthand contracts) or by the type
checker (for purely logical contracts).

Example:

```
contracts {
  requires domains [corporate, sanctions];
  ensures  domains [corporate];
}
```

Domain shorthand references compliance domains the host recognizes. The
language itself assigns no semantics to a specific domain name; it carries
the shorthand through to the host layer.

## 6. Compensation

Compensation mirrors the execution semantics of long-running economic
workflows: it is reverse-topological, step-idempotent, best-effort across
multiple inverse actions, and persisted after each successful inverse.

- **Ordering.** Compensation order is reverse-topological on the forward
  DAG.
- **Locality.** A step's `compensate { ... }` clause attaches to the step it
  inverts. The compiler emits a detached rollback plan when targeting a
  runtime that expects one.
- **Idempotency.** Every compensation branch must be idempotent with respect
  to step status and the external side effect it inverts.
- **Best-effort.** When one inverse action fails, the compiler emits the
  plan so that independent inverse actions still run. The failed branch is
  recorded for operator attention.
- **Evidence invalidation.** A step may declare `invalidated_domains` in
  its compensation clause. Attestation records whose domains overlap the
  declared set are marked revoked by the host when the rollback runs.

## 7. Multi-Entity Operations

Op has first-class support for operations with more than one participating
entity. Participants declare their role, entity, and governance
requirements.

**Roles.** `Acquirer`, `Target`, `Partner`, `SourceZone`, `DestinationZone`,
`Participant`.

**Governance requirements.**

- `BoardResolution { quorum, required_roles }`
- `ShareholderVote { threshold_bps }`
- `RegulatoryApproval { authority }`

**Approval modes.** `unanimous`, `majority`, `bilateral`, and
`specific(<required>)`.

**Composition law.** A host that composes compliance verdicts across
participants must do so by the meet operation on its compliance lattice —
the most restrictive participant's verdict wins. The language enforces that
the host's composition is honored in the step ordering; it does not
prescribe the lattice.

## 8. Jurisdiction Resolution

Every Op program has one ambient jurisdiction. The ambient jurisdiction
participates in registry resolution, obligation selection, and host
context construction.

**Canonicalization.** The host canonicalizes jurisdiction identifiers before
type-checking. Aliases such as `florida` (→ `us-florida`) or `BVI` (→
`vg-bvi`) normalize through the host.

**Fallback.** A program may author a generic `_default` body or a
jurisdiction-specific body. Lowering preserves the runtime's fallback rule:
exact match first, `_default` second.

**Scoped jurisdiction.** A cross-zone workflow may rebind the ambient
jurisdiction inside a scope block:

```
in seller_zone { ... }
in buyer_zone  { ... }
```

The compiler must preserve the scope faithfully. Silent erasure of a
semantically relevant jurisdiction switch is forbidden.

## 9. Gas

Op has a two-tier gas model.

- **Structural gas** is bounded statically by the program shape. The
  compiler assigns each construct a constant cost and sums over the body.
  A program with a statically-bounded structural gas cost can be admitted
  or rejected at submit-time.
- **Extensional gas** is metered at runtime. A program whose execution
  cost depends on cardinalities (list length, syscall volume, storage
  growth) may carry a cardinality certificate attesting that at a given
  attestation time the query returns at most `n` elements. The extensional
  gas bound is then `per_element_gas * n`.

A host embedder may replace the structural cost table to match its
deployment economics.

## 10. Policy Blocks

Some hosts expose a proof backend (a virtual machine that compiles a policy
and verifies its satisfaction against host state). Op represents these
interactions as explicit `policy` blocks:

```
policy trade_gate using savm {
  prove domains [trade, sanctions, banking];
}
```

The policy block is a language-level annotation. The host compiles and
evaluates it through its own proof backend; Op does not prescribe the
backend.

## 11. Host ABI

Every side effect flows through the `OpHost` trait supplied by
`op-core::host`. A host implements:

```rust
fn invoke(&self, call: &PrimitiveCall) -> Result<HostOutcome, HostError>;
fn canonicalize_jurisdiction(&self, raw: &str) -> String;
fn discharge_safety(
    &self,
    predicate: &SafetyPredicate,
    context: &serde_json::Value,
) -> Result<(), HostError>;
```

`PrimitiveCall` carries the primitive name, reduced JSON arguments, and
the ambient jurisdiction. `HostOutcome` is either `Completed(Value)` or
`Waiting { event, resume_token }`. A deterministic host returns the same
outcome for the same call on every replay; replay verification depends on
this property.

A `NoopHost` ships in the crate for tests and examples — it echoes every
call as a deterministic JSON record. A production embedding replaces
`NoopHost` with a kernel-backed host that executes primitives against
sovereign state.

## 12. Grammar

The following EBNF is intentionally compact. It is concrete enough to parse
and define the user-facing surface.

```ebnf
program        = header, metadata*, section*, "do", block ;
header         = "op", op_name, "for", jurisdiction_ref ;
metadata       = version_decl | description_decl ;
version_decl   = "version", string ;
description_decl = "description", string ;

section        = inputs | outputs | types | participants | effects | contracts ;
inputs         = "inputs", record_type_block ;
outputs        = "outputs", record_type_block ;
types          = { "type", ident, "=", type_ref } ;
participants   = "participants", "{", participant_decl+, "}", approval_decl? ;
participant_decl = ident, ":", participant_role, "(", expr, ")", governance_clause?, ";" ;
participant_role = "Acquirer" | "Target" | "Partner" | "SourceZone" | "DestinationZone" | "Participant" ;
governance_clause = "requires", governance_req, { "+", governance_req } ;
governance_req = "BoardResolution", "{", "quorum", ":", string, ",", "required_roles", ":", string_list, "}"
               | "ShareholderVote", "{", "threshold_bps", ":", integer, "}"
               | "RegulatoryApproval", "{", "authority", ":", string, "}" ;
approval_decl  = "approval", ("unanimous" | "majority" | "bilateral" | ("specific", "(", string_list, ")")), ";" ;

effects        = "effects", "{", effect_decl+, "}" ;
effect_decl    = effect_name, ";" ;
effect_name    = "sovereign_write" | "identity_mutation" | "fiscal_transfer"
               | "sanctions_check" | "governance_request" | "document_generation"
               | "external_read" | "proof_emit" | ("await", callback_event) ;

contracts      = "contracts", "{", require_decl?, ensure_decl?, "}" ;
require_decl   = "requires", contract_expr, ";" ;
ensure_decl    = "ensures", contract_expr, ";" ;
contract_expr  = ("domains", "[", ident, { ",", ident }, "]") | boolean_expr ;

block          = "{", statement*, "}" ;
statement      = let_stmt | step_stmt | run_stmt | par_stmt | choose_stmt
               | in_stmt | policy_stmt | return_stmt ;
let_stmt       = "let", ident, ":", type_ref, "=", expr, ";" ;
run_stmt       = "run", ident, "=", expr, ";" ;
return_stmt    = "return", expr, ";" ;
step_stmt      = "step", ident, ":", type_ref, "->", type_ref, "!", effect_set, step_body, compensation_clause? ;
step_body      = block | primitive_call ;
compensation_clause = "compensate", block ;
primitive_call = primitive_name, "(", arg_list?, ")" ;
par_stmt       = "par", "{", (ident, "=", expr, ";")+, "}" ;
choose_stmt    = "choose", "{", ("when", boolean_expr, "->", block)+, ("else", "->", block)?, "}" ;
in_stmt        = "in", jurisdiction_ref, block ;
policy_stmt    = "policy", ident, "using", ident, block ;

expr           = literal | ident | field_access | call_expr | record_expr | list_expr | await_expr | string ;
await_expr     = "await", callback_event, "within", duration ;
field_access   = expr, ".", ident ;
call_expr      = ident, "(", arg_list?, ")" ;
record_expr    = "{", (ident, ":", expr, { ",", ident, ":", expr })?, "}" ;
list_expr      = "[", (expr, { ",", expr })?, "]" ;
arg_list       = expr, { ",", expr } ;
boolean_expr   = expr, bool_op, expr | "not", expr | "(", boolean_expr, ")" ;
bool_op        = "==" | "!=" | ">" | ">=" | "<" | "<=" | "and" | "or" | "in" | "contains" ;

type_ref       = scalar_type | "[", type_ref, "]" | type_ref, "?"
               | "(", type_ref, { ",", type_ref }, ")"
               | "{", (ident, ":", type_ref, { ",", ident, ":", type_ref })?, "}"
               | "Result", "<", type_ref, ",", type_ref, ">"
               | "Await", "<", callback_event, ",", type_ref, ">"
               | ident ;
scalar_type    = "EntityId" | "JurisdictionId" | "MoneyAmount"
               | "ContentDigest" | "StepId" | "CallbackEventType"
               | "String" | "Bool" | "Int" | "Date" | "Timestamp" | "Duration" ;

primitive_name = ident, { ".", ident } ;
op_name        = ident, { ".", ident } ;
callback_event = ident, ".", ident, { ".", ident } ;
jurisdiction_ref = ident | string ;
literal        = string | integer | "true" | "false" | "null" ;
string_list    = "[", string, { ",", string }, "]" ;
duration       = integer, ("d" | "h" | "m" | "s") ;
```

## 13. Worked Examples

Four worked examples ship with the repository:

- `crates/op-core/examples/hello-op.rs` — a 60-second cold-reader tour:
  parse, typecheck, execute, render a compliance-carrying verdict.
- `crates/op-core/examples/compliance-gate.rs` — a rule-aware host
  denying a transfer when the counterparty jurisdiction is sanctioned
  and the amount exceeds a low-value threshold; shows the proof
  certificate shape.
- `examples/incorporate.op` — minimum entity incorporation for a
  single jurisdiction.
- `examples/letter-of-credit.op` — bilateral cross-zone trade finance
  with scoped jurisdiction blocks and a policy block.

The `.op` surface-syntax examples compile against the canonical primitive
corpus in `op-stdlib`.
