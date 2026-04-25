# Op: The Supremum Design

## 1. What Op is

Op is a typed, stack-based bytecode and deterministic small-step operational
semantics for compliance-carrying operations in sovereign institutional
kernels. The paper specifies the ideal bytecode surface: typed steps with an
explicit effect row, precondition and postcondition contracts, scoped
compensation attached to the step it inverts, typed suspension and resumption
for callback events, canonical byte encoding, and a proof bundle sufficient
to replay the operation on a conforming evaluator.

The repository intentionally separates three artifacts:

1. **Specification.** The paper fixes the CBOR/BLAKE3, indexed-typestate,
   proof-bundle, and replay semantics.
2. **Executable prototype.** The Rust crates expose the AST, current type
   checker, effect-safety analyzer, gas model, evaluator, host trait, JSON
   parser, YAML lowering, and Lex->Op compiler. The executable wire surface
   is not yet the full canonical CBOR bytecode.
3. **Mechanization.** Coq files prove scoped subclaims: nine Lex->Op
   compilation cases, abstract bilateral session skeletons, abstract BSC
   history invariants, and several lattice/encoding scale models. Full
   Op-proper type soundness and full-surface bytecode canonicity remain open.

Every replay claim below should be read with the full replay precondition:
the verifier needs the program bytes, inputs, pack digest, and oracle log
(external reads, callback payloads, and deadline events). Replay without the
oracle log is undefined.

This file is part of the repository operating architecture with
`SUPREMUM-DISCIPLINE.md`, `AGENTS.md`, and `CLAUDE.md`. If the specified
calculus, executable status, mechanization status, repository layout, or
public-reference boundary changes, update those paired surfaces in the same
change.

Lex, the rule language for jurisdictional compliance, compiles into Op: a
Lex predicate becomes an Op boolean expression, a Lex defeasible rule
becomes a guarded `choose`, a Lex verdict becomes an Op `ensures domains`
declaration. Op does not re-interpret Lex semantics at runtime; compilation
is content-addressed and pinned at authoring time. The outputs are a
workflow whose execution trace is its audit, a replay protocol that verifies
another kernel's claim byte-for-byte, and five conservation invariants that
are specified by the calculus and currently mechanized only on the scoped
subsystems named below.

## 2. Grammar primitives

Op lifts five institutional-workflow primitives from library idiom to
language grammar.

**Typed effect rows with sanctions dominance.** Nine tracked effects —
`sovereign_write`, `identity_mutation`, `fiscal_transfer`, `sanctions_check`,
`governance_request`, `document_generation`, `external_read`, `proof_emit`,
and `await <event>` — form a lattice under union. Each step carries an
effect row `E ⊆ 2^{Effect}` in its signature `In → Out ! E`; sequential
composition `a ; b` takes effect row `E_a ∪ E_b`. A reachable write-class
effect (`sovereign_write`, `identity_mutation`, `fiscal_transfer`) must be
dominated in the control-flow DAG by a `sanctions_check` in the same branch,
with a narrow deferred-subject exception for entity creation where the
subject does not yet exist. The rule is syntactic and structural: the type
checker rejects programs whose effect row has a reachable write without a
dominating check.

**Scoped compensation.** A `compensate { ... }` clause attaches lexically to
the step it inverts. The compiler derives the reverse-topological rollback
plan from the forward DAG: on step failure, inverse actions run in reverse
completion order, each idempotent, each best-effort so that independent
inverse actions still run when one fails. A compensation branch may declare
`invalidated_domains`; the host revokes attestation records whose domains
overlap the declared set when the rollback runs. Compensation cannot attach
to a step with no compensable effect; the type checker rejects the program.

**Typed suspension via `await ... within`.** An awaiting step returns
`Await<Event, Payload>`. A downstream step that treats an `Await<E, P>` as
if it were `P` fails to type-check. The continuation is serialized into the
proof bundle, so suspension is as replayable as ordinary computation.

**Linear and indexed corridor resources.** The specified calculus has
`Linear<T>` plus indexed corridor typestates `Locked<T, omega, epsilon>`,
`Signed<V, omega, epsilon>`, `Verified<omega, epsilon>`, and
`Blame<Z, omega, epsilon>`. The current Rust AST still exposes an
unindexed `Locked<T>` prototype; indexed enforcement is a frontier item.

**Bilateral session-typed cross-zone 3PC.** The proved corridor result is
binary: Initiator and Responder endpoints under the
Honda-Vasconcelos-Kubo discipline. The Coq proof is payload-parametric and
covers the bilateral message skeleton; concrete payload integration and
full n-party MPST merge/recursion remain open. The n-party examples are
design targets, not closed theorems.

## 3. Operational semantics

Op is specified by a small-step reduction relation
`(e, σ, μ, G, C) →ᵝ (e', σ', μ', G', C')`, where

- `e` is the expression under reduction,
- `σ` is the typed store (bindings, linear-resource states, lock states),
- `μ` is the append-only audit ledger,
- `G = (g_s, g_x)` is the two-axis gas state (structural and extensional
  units consumed),
- `C` is the compensation stack (reverse-topological plan of inverse
  actions for committed effects),
- `β ∈ Label` is the transition label: either `τ` (silent) or an observable
  `emit(v)`.

**Evaluation contexts.** Reduction under evaluation contexts `E[·]` is
left-to-right within sequential composition, unordered within `par` branches
that share no data dependency, and guarded by boolean reduction inside
`choose`. `await e within d` is a reduction point; a reached `await`
transitions the configuration to a suspended form carrying a resume token
threaded into the proof bundle.

**Terminal set.** A configuration is terminal in one of seven forms:

1. `ADMIT(verdict)` — completed positive verdict value.
2. `DENY(reason)` — completed negative verdict.
3. `AWAIT(token, deadline)` — typed suspension point.
4. `COMPENSATED(trace)` — compensation stack ran to completion after a
   step failure.
5. `ABORTED(obstruction)` — kernel halted the execution on a threatened
   conservation invariant.
6. `GAS_EXHAUSTED(axis)` — a static or runtime gas bound was exceeded.
7. `STUCK` — no reduction rule applies and no verdict emitted; unreachable
   in well-typed programs (see Progress).

**Type soundness.** Three lemmas are stated for the specified Op calculus.
They are not yet mechanized over Op proper; current Coq coverage is over
toy/core fragments and parametric interfaces.

- **Progress.** If `Γ ⊢ e : T ! E` and `(e, σ, μ, G, C)` is not terminal,
  there exists `(e', σ', μ', G', C')` with `(e, σ, μ, G, C) → (e', ...)`.
- **Subject reduction.** If `Γ ⊢ e : T ! E` and
  `(e, σ, μ, G, C) → (e', σ', μ', G', C')`, then `Γ ⊢ e' : T ! E'` with
  `E' ⊆ E`, where strict inclusion arises from discharged effects.
- **Effect monotonicity.** Effects discharged by prior steps carry forward
  as audit entries in `μ` and never silently disappear; the composed row
  upward-bounds the remaining effect row at every reduction frontier.

Progress and subject reduction are the standard type-soundness pair adapted
to the configuration tuple. The full proof requires the real Op expression
semantics, kappa-threading, linear resources, compensation, suspension,
`par`, and `choose`; that integration is open.

## 4. Conservation invariants

Five conservation invariants are the specified target. Today they are
proved only in scoped models, not as one full theorem over Op proper.

**Gas conservation.** Structural gas consumed plus structural gas remaining
equals the static structural gas bound emitted by the type checker.
Extensional gas consumed plus extensional gas remaining equals the bound
computed at submit-time from attached cardinality certificates. No
reduction step mints or destroys gas except by metered consumption.

**Resource linearity.** In the specified calculus, every `Linear<T>` is
consumed exactly once on complete executions and every
`Locked<T, omega, epsilon>` is eliminated by the commit or release path.
The current executable checker rejects double consumption but does not yet
enforce the full indexed exactly-once discipline at scope exit.

**Ownership conservation.** For every ownership claim in the store `σ`,
the sum of claims across entities is invariant under reduction except at
steps carrying `fiscal_transfer` in their effect row; there the delta is
typed by `MoneyAmount` and signed so that per-currency totals are preserved
across the transfer.

**Audit monotonicity.** The audit ledger `μ` is append-only: if
`(e, σ, μ, G, C) → (e', σ', μ', G', C')`, then `μ` is a prefix of `μ'`.
Monotonicity holds syntactically (the prefix relation) and semantically
(the composed verdict is the pointwise meet on the compliance lattice, and
adding a participant can only tighten the verdict). Compensation appends a
revocation record; it does not edit or delete.

**Meet-monotonicity under corridor translation φ.** When an Op execution
crosses a corridor `(R, φ)` into a second zone, the receiving-zone verdict
is the image of the sending-zone verdict under φ, pointwise-meet with
receiving-zone obligations. Tightening the sending-zone verdict tightens
the composed verdict. The translation is part of the corridor's typed
state and is replay-checked against the proof bundle.

## 5. Gas model

Op meters execution on two axes.

**Structural gas** is bounded by program shape. The paper states a
small-step fuel model; the Rust prototype currently uses a configurable
AST/statement cost table (`step_cost`, `run_cost`, branch costs) rather than
the effect-specific 8/4 schedule used in older notes. Unifying the paper
fuel model and executable table is an open alignment item.

**Extensional gas** is metered at runtime. A program whose execution cost
depends on cardinalities that cannot be statically bounded — list length,
syscall volume, storage growth — attaches a cardinality certificate
attesting that a specified query returns at most `n` elements at the
declared attestation time. The bound is `per_element_gas · n`. The runtime
deducts metered cost at each cardinality-sensitive primitive; exhaustion
transitions the configuration to `GAS_EXHAUSTED(extensional)`.

**Compensation budget sub-allocation.** A fraction of the structural gas
budget is reserved for compensation. A program that commits a compensable
effect reserves the budget its rollback needs at commit; on compensation,
the reserve is drawn down. A rollback cannot run out of structural gas on
a well-typed program. The reserve is a sub-axis of structural gas; the
conservation invariant covers its sum.

## 6. Session-type framing of cross-zone 3PC

A cross-zone Op execution in the proved core is bilateral. The global
session type `G_corridor` specifies the protocol between a sending zone `S`
and a receiving zone `R` mediated by a corridor `(R, phi)`:

```
G_corridor ≔
  S → R : LockRequest(payload: Linear<T>) .
  R → S : LockGrant(witness: Locked<T>) .
      ( S → R : Commit(witness_foreign_minted) .
        R → S : Ack .
        end
      | S → R : Release(witness_foreign_aborted) .
        R → S : Ack .
        end
      )
```

`G_corridor` is a standard branching session type under the
Honda-Vasconcelos-Kubo discipline. The endpoint projections
`G_corridor ↾ S` and `G_corridor ↾ R` are the two participant session types;
a well-typed Op program at each endpoint conforms to its projection.

**Linear `Locked<T, omega, epsilon>` resource.** The specified indexed
typestate is the static witness of the grant phase. In the current Coq BSC
model, lock/sign/verify/blame/timeout preserve abstract history invariants
I1-I3. Distinct commit and release operational rules over the real Op
semantics remain open.

**Deadlock-freedom.** Under the binary endpoint-projection discipline, the
payload-parametric skeleton does not deadlock on the session layer. Residual
liveness depends on delivery, timeout/tick events, and Byzantine enforcement
outside the type system.

**Session safety.** The composed bilateral skeleton preserves the projected
session type. No claim is made here that the current mechanization derives
commit/abort agreement from independently computed local decisions; that
requires concrete payload and decision-function integration.

## 7. Lex→Op compilation

Lex is the rule-and-proof layer; Op is the workflow layer. Their interface
is preconditions, postconditions, and effect discharge. The compilation
function `⟦·⟧ : Lex → Op` is defined by structural induction over the
admissible fragment of Lex. Six cases cover the §6.2 rules:

1. **`const`.** A scalar or compound constant lifts pointwise through
   `lift_value : LexValue → OpExpr`. Scalar: unit, boolean, integer,
   string. Compound: records (pointwise on named fields), lists
   (pointwise on elements), variants (tag plus lifted payload).
2. **`var`.** A variable reference against a shared prelude compiles to
   the Op variable form. Both languages read from the same deterministic
   prelude.
3. **`match`.** A match on a scalar scrutinee with nullary-constructor
   patterns and scalar-constant branch bodies compiles to a `choose` over
   lifted branches, with a fail-closed sentinel (`"pattern_unmatched"`)
   for the unmatched case.
4. **`defeasible`.** A defeasible rule with scalar-constant base, boolean
   guards, and scalar-constant exception bodies compiles to a `choose`
   over the exception list pre-sorted by
   `(priority DESC, source_position ASC)` with the lifted base as the
   `else` arm.
5. **`sanctions`.** A sanctions-dominance rule with scalar-constant
   principal compiles to a host call `sanctions.check` in a
   `sanctions_check` effect row, consumed by a downstream read of the
   two-valued result (`"Compliant"` or `"SanctionsBlocked"`).
6. **`fill`.** A hole-fill reduction writes a filler witness into the
   attestation ledger; compilation preserves verdict semantics modulo a
   single bisimulation step threading the `τ` attestation-append.

**Admissible fragment.** A Lex term is admissible when it lies in the
positive fragment generated by the six cases: constants, prelude variables,
matches on scalar scrutinees with nullary patterns and scalar branch
bodies, defeasible rules with boolean guards and scalar exception bodies,
sanctions-dominance against a scalar principal, hole-fills writing scalar
fillers. Compound constants are admissible at field level when their
fields are admissible.

**Verdict-preservation theorem.** For every term in the current scalar
admissible skeleton:
`lex_verdict(t) = v ⇔ op_verdict(⟦t⟧) = v`.

**Coq mechanization status.** Nine of nine compilation cases close with
`Qed.` under Rocq Prover 9.1.1 in `formal/coq/CompilationSoundness.v`:
scalar constant, sanctions-dominance, variable, record constant, list
constant, variant constant, match, defeasible, and hole-fill. The theorem
statements are narrow: sanctions and variables depend on disclosed
Parameters (`host_sanctions`, `prelude`), the defeasible theorem preserves
the supplied exception order after sorting has already been done, and
hole-fill preserves the attestation-append skeleton rather than the full
PCAuth validation protocol.

## 8. Implementation and repository state

The Rust workspace has four crates:

- `op-core` — language core: AST, current type checker, effect-row algebra
  with the sanctions-dominance analyzer, two-tier gas model, deterministic
  evaluator over the host-abstraction trait, JSON wire-format parser.
- `op-compiler` — YAML and source-language lowering to the Op AST, with
  FNV-1a content addressing.
- `op-stdlib` — canonical primitive corpus for the five kernel primitive
  families (Entities, Ownership, Fiscal, Identity, Consent) with typed
  signatures and default effect rows.
- `op-lex-compiler` — implementation of the six §6.2 compilation cases
  (`case_const`, `case_var`, `case_match`, `case_defeasible`,
  `case_sanctions`, `case_fill`), with the lift function `lift_value` and
  an admissibility checker.

The executable inventory and expected test counts are defined by
`REPRODUCIBILITY.md`. Benchmark harnesses exist in the workspace; any
published performance table is a measured snapshot and not a formal claim.

An initial release is tagged. GitHub Actions CI runs Rust and Rocq
pipelines on every push. The workspace compiles standalone from a cold
clone with no path dependencies on sibling checkouts; pinned toolchain at
`rust-toolchain.toml`. The benchmark table above is reproducible with the
commands in `REPRODUCIBILITY.md` and `docs/benchmarks.md`.

## 9. Prior art

Op occupies the intersection of typed bytecode, effectful workflow
calculus, and session-typed distributed protocol.

- **EVM** (Wood, 2014). Typed stack bytecode, deterministic execution,
  metered gas. Differs: no effect system, no linear resources, no
  session-typed cross-zone protocol; compliance is a host concern.
- **WebAssembly** (Haas et al., 2017). Typed bytecode, deterministic
  execution, formal small-step semantics, linear-memory discipline.
  Differs: no audit ledger, no compensation, no typed suspension; side-
  effectful host calls are opaque.
- **Michelson** (Allombert et al., 2018). Typed stack language with formal
  operational semantics for on-chain smart contracts. Differs: transaction-
  atomic, no non-atomic suspension or cross-zone commit, no effect row
  over institutional primitives.
- **Yul** (Solidity team). Intermediate representation for EVM and eWasm
  with typed values. Differs: compilation IR without effect system or
  conservation invariants.
- **Move** (Blackshear et al., 2019). Linear-resource discipline for
  on-chain assets. Differs: no effect rows, no cross-zone session
  protocol. Op adopts the linear-resource discipline wholesale and extends
  with `Locked<T>` for multi-zone commit.
- **CakeML** (Kumar et al., POPL 2014). Verified ML with mechanized
  compiler and operational semantics. Differs in target: general-purpose
  pure functional programs vs. Op's compliance-carrying workflows with
  effect and resource discipline.
- **CompCert** (Leroy, 2009). End-to-end verified C compiler with
  mechanized preservation. Op's verdict-preservation theorem is the
  workflow-language counterpart.
- **Sagas / BPEL**. Sagas (Garcia-Molina and Salem, 1987) introduced
  reverse-topological compensation for long-lived transactions; BPEL 2.0
  (OASIS) standardized compensation handlers attached to scopes. Op
  differs: compensation is scoped syntactically to the step it inverts and
  validated by the type checker, not an orchestration runtime discipline.
- **Temporal / Cadence** (Uber / Temporal.io). Durable workflow
  orchestrators with replayable execution logs. Differs: execution
  semantics are an SDK implementation rather than a typed small-step
  calculus, and the effect discipline is not mechanized.
- **Honda-Vasconcelos-Kubo session types** (ESOP 1998). Binary session
  types for deadlock-free typed communication. Op lifts the discipline to
  cross-zone 3PC via `G_corridor` and `Locked<T>`.
- **Wadler, propositions as sessions** (ICFP 2012); **Caires-Pfenning**
  (CONCUR 2010). Intuitionistic-logic session types. Op uses the
  projection-conformance discipline; the logical interpretation informs
  the linear-resource framing of the lock phase.
- **Bauer-Pretnar algebraic effects** (JLAMP 2015); **Koka** (Leijen,
  Microsoft Research). Row-polymorphic effect systems with handler
  discharge. Op's effect row is row-shaped; the sanctions-dominance law
  is a lattice constraint on the row rather than a handler discipline.
- **Necula, Proof-Carrying Code** (POPL 1997). Bytecode carrying a safety
  proof. Op's proof bundle carries the replay witness; the verifier runs
  the program against the bundle and compares digests. Op's conservation
  invariants are the structural counterpart of the PCC safety predicate.
- **CompCertTSO** (Ševčík et al., POPL 2011). Verified compilation under
  relaxed memory. Op is sequentially consistent within a zone and cross-
  zone-ordered by session type, so the relaxed-memory questions
  CompCertTSO addresses do not arise in Op's execution model.

Op's contribution is the combination: typed effects with a sanctions-
dominance law, typed suspension, local compensation, linear and indexed
corridor resources, and binary session-typed cross-zone execution, as
primitive grammar. The mechanized core today is the scoped
verdict-preservation theorem plus the abstract bilateral/BSC/lattice
subsystems; the full Op-proper soundness pair is open.

## 10. Open problems

**PCAuth validation.** The `fill` compilation case is Qed-closed for the
attestation-append skeleton, but full PCAuth validation is not part of that
theorem. The remaining work is to index fill witnesses by pack version,
model `VerifyPCAuth`, reject invalid witnesses explicitly, and prove the
validated transport theorem.

**Extended metatheory.** Termination, Progress, Subject Reduction, Effect
Monotonicity, and Parallel Confluence are stated over the configuration
tuple. Full mechanization over Op proper is open.

**Byzantine 3PC watcher layer.** The session-type discipline gives
deadlock-freedom on well-typed participants. Byzantine behavior (message
forgery, arbitrary protocol deviation) falls outside the type system and
is addressed by a cryptographic watcher layer: each message carries a
signature verifiable against the corridor's attestation epoch; liveness
under partition is bounded by the configured timeout plus the watcher's
resolution time. Formalization as a companion protocol is open.

**Zero-knowledge compilation.** The admissible Lex fragment is compilable
to a zero-knowledge circuit proving verdict preservation without revealing
the scrutinee. Each §6.2 case has a fixed arithmetic shape, providing a
useful starting point; full compilation path is open.

**Performance under production load.** Microbenchmarks on a single M4
Max do not exercise realistic primitive backends (kernel-backed host,
network-reachable sanctions services, registry filings) that stress
extensional gas accounting and proof-bundle serialization. Measurement
against a kernel-backed host is an open evaluation item.

## 11. Ecosystem role

Op is the operational substrate for Lex rules. The sovereign institutional
kernel is a proof-producing rule engine: jurisdictional obligations
expressed in Lex compile into Op under the §6.2 rules; the kernel
dispatches Op programs through the `OpHost` trait against sovereign state
— entity registries, ownership graphs, fiscal ledgers, identity stores,
consent records. Cross-zone replay is the corridor's verification
primitive: the receiving zone re-runs the sending zone's Op program
against the same inputs, pack digest, and oracle log, compares proof
bundles digest-by-digest, and the corridor-translation phi maps the
sending-zone verdict into the receiving-zone compliance lattice. Production
embedders instantiate `OpHost` against their own compliance packs,
jurisdictional registries, and attestation backends. The open-source Op tree
ships the language surface, current executable prototype, host trait,
canonical corpus, and scoped Coq mechanization.

## 12. References

Allombert, V., Bourgoin, M., and Tesson, J. (2018). *Michelson: The
Language of Smart Contracts in Tezos*. Tezos Foundation.

Bauer, A. and Pretnar, M. (2015). Programming with algebraic effects and
handlers. *JLAMP* 84(1), 108–123.

Blackshear, S. et al. (2019). *Move: A Language With Programmable
Resources*. Libra Association.

Caires, L. and Pfenning, F. (2010). Session types as intuitionistic
linear propositions. *CONCUR 2010*, 222–236.

Garcia-Molina, H. and Salem, K. (1987). Sagas. *SIGMOD '87*, 249–259.

Haas, A. et al. (2017). Bringing the web up to speed with WebAssembly.
*PLDI 2017*, 185–200.

Honda, K., Vasconcelos, V. T., and Kubo, M. (1998). Language primitives
and type disciplines for structured communication-based programming.
*ESOP 1998*, 122–138.

Kumar, R., Myreen, M. O., Norrish, M., and Owens, S. (2014). CakeML: A
verified implementation of ML. *POPL 2014*, 179–191.

Leijen, D. (2014). *Koka: Programming with row-polymorphic effect types*.
Microsoft Research.

Leroy, X. (2009). Formal verification of a realistic compiler.
*Communications of the ACM* 52(7), 107–115.

Necula, G. C. (1997). Proof-carrying code. *POPL '97*, 106–119.

OASIS (2007). *Web Services Business Process Execution Language*. OASIS
Standard (BPEL 2.0).

Ševčík, J., Vafeiadis, V., Zappa Nardelli, F., Jagannathan, S., and
Sewell, P. (2011). CompCertTSO: A verified compiler for relaxed-memory
concurrency. *POPL 2011*, 43–54.

Wadler, P. (2012). Propositions as sessions. *ICFP 2012*, 273–286.

Wood, G. (2014). *Ethereum: A Secure Decentralised Generalised
Transaction Ledger*. Ethereum Foundation, Yellow Paper.
