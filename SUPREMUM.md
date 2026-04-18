# Op: The Supremum Design

## 1. What Op is

Op is a typed, stack-based bytecode and deterministic small-step operational
semantics for compliance-carrying operations in sovereign institutional
kernels. A program is a directed acyclic graph of typed steps with an
explicit effect row, precondition and postcondition contracts, a scoped
compensation branch attached to the step it inverts, and explicit suspension
and resumption semantics for callback events. Reduction is metered by a
two-axis gas model separating structural cost from extensional cost. Every
execution produces a content-addressed proof bundle sufficient to replay the
operation on any kernel that shares the program definition and the inputs.
Lex, the rule language for jurisdictional compliance, compiles into Op: a
Lex predicate becomes an Op boolean expression, a Lex defeasible rule
becomes a guarded `choose`, a Lex verdict becomes an Op `ensures domains`
declaration. Op does not re-interpret Lex semantics at runtime; compilation
is content-addressed and pinned at authoring time. The outputs are a
workflow whose execution trace is its audit, a replay protocol that verifies
another kernel's claim byte-for-byte, and five conservation invariants that
hold by construction.

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

**Linear and locked resources.** Two type constructors model single-use
resources and two-phase commit locks. `Linear<T>` consumes at most once; a
program that consumes a linear resource twice fails to type-check.
`Locked<T>` is a resource in a locked state with exactly two eliminators:
`commit_transfer(witness_foreign_minted)` consumes, and
`release_lock(witness_foreign_aborted)` restores the resource to
`Linear<T>`. The typestate is tracked statically; a program that fails to
consume a `Locked<T>` resource with exactly one of the two eliminators
fails to type-check.

**Multi-party session-typed cross-zone 3PC.** A cross-zone operation is
typed as a global session between two or more sovereign kernels. The
session-type discipline supplies deadlock-freedom and session safety by
construction; the `Locked<T>` typestate lifts the three-phase-commit
protocol into a static invariant. Section 6 formalizes.

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

**Type soundness.** Three lemmas hold on well-typed Op programs; the
mechanization tree is rooted at `formal/coq/CompilationSoundness.v`.

- **Progress.** If `Γ ⊢ e : T ! E` and `(e, σ, μ, G, C)` is not terminal,
  there exists `(e', σ', μ', G', C')` with `(e, σ, μ, G, C) → (e', ...)`.
- **Subject reduction.** If `Γ ⊢ e : T ! E` and
  `(e, σ, μ, G, C) → (e', σ', μ', G', C')`, then `Γ ⊢ e' : T ! E'` with
  `E' ⊆ E`, where strict inclusion arises from discharged effects.
- **Effect monotonicity.** Effects discharged by prior steps carry forward
  as audit entries in `μ` and never silently disappear; the composed row
  upward-bounds the remaining effect row at every reduction frontier.

Progress and subject reduction are the standard type-soundness pair adapted
to the configuration tuple. Effect monotonicity closes the gap between
static effect rows and the runtime audit ledger: ordinary soundness only
guarantees the remaining computation stays well-typed, whereas effect
monotonicity records that discharged effects have observable audit
footprints and cannot be shed.

## 4. Conservation invariants

Five conservation invariants hold on every well-typed Op execution by
construction.

**Gas conservation.** Structural gas consumed plus structural gas remaining
equals the static structural gas bound emitted by the type checker.
Extensional gas consumed plus extensional gas remaining equals the bound
computed at submit-time from attached cardinality certificates. No
reduction step mints or destroys gas except by metered consumption.

**Resource linearity.** Every `Linear<T>` is consumed by exactly one
consuming step on every complete execution; every `Locked<T>` is eliminated
by exactly one of `commit_transfer` or `release_lock`. A program that
violates linearity fails to type-check; a dynamic state transition that
would violate linearity is a non-step.

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

**Structural gas** is bounded statically by program shape. The compiler
sums constant costs drawn from a structural cost table over the program
body: a `sovereign_write` step costs 8 units, a `sanctions_check` gate 4,
a `par` branch the sum of its siblings, a `choose` the maximum over its
arms, an `await` a fixed suspension-record cost. A program whose
structural gas exceeds a submit-time threshold is rejected at submit-time.
The embedder may replace the cost table to match deployment economics.

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

A cross-zone Op execution that spans two or more sovereign kernels is typed
as a global session. The global session type `G_corridor` specifies the
protocol between a sending zone `S` and a receiving zone `R` mediated by a
corridor `(R, φ)`:

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

**Linear `Locked<T>` resource.** The `Locked<T>` typestate is the static
witness of the grant phase. Between `LockGrant` and one of `Commit`,
`Release`, the resource is in state `Locked<T>`; after `Commit` the
resource is consumed; after `Release` the resource returns to `Linear<T>`
and may be re-submitted. Exactly one of the two eliminators fires on a
well-typed execution; neither firing nor double-firing is expressible.

**Deadlock-freedom.** Under the endpoint-projection discipline, a
multi-party session that admits duality of projections does not deadlock
on well-typed participants. Op inherits the result: a cross-zone execution
at well-typed endpoints does not deadlock on the session layer. Residual
deadlock risk is at the infrastructure layer (message-delivery liveness,
Byzantine participant behavior) and is addressed by the watcher layer
rather than the type system; see Section 10.

**Session safety.** The composed execution preserves the global session
type: no message arrives out of order, no message is received that the
protocol does not admit, and every send has a matching receive in the dual
endpoint. Session safety is a corollary of endpoint-projection conformance
at each participant plus the linearity of `Locked<T>`.

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

**Verdict-preservation theorem.** For every admissible Lex term `t`:
`lex_verdict(t) = v ⇔ op_verdict(⟦t⟧) = v`.

**Coq mechanization status.** Eight of nine compilation cases close with
`Qed.` under Rocq Prover 9.1.1 with zero admitted axioms, in
`formal/coq/CompilationSoundness.v`: scalar constant, sanctions-dominance,
variable, record constant, list constant, variant constant, match, and
defeasible. The remaining obligation is `HoleFill (§6.3)`; the strategy is
coinduction on a bisimulation relation pairing each Lex state with the Op
state reached by unwinding one `τ` attestation-append step. The obligation
is registered as an open theorem in the `Obligations` section at the foot
of `CompilationSoundness.v`.

## 8. Implementation and repository state

The Rust workspace has four crates:

- `op-core` — language core: AST, bidirectional type checker with
  linearity tracking, effect-row algebra with the sanctions-dominance
  analyzer, two-tier gas model, deterministic evaluator over the
  host-abstraction trait, JSON wire-format parser.
- `op-compiler` — YAML and source-language lowering to the Op AST, with
  FNV-1a content addressing.
- `op-stdlib` — canonical primitive corpus for the five kernel primitive
  families (Entities, Ownership, Fiscal, Identity, Consent) with typed
  signatures and default effect rows.
- `op-lex-compiler` — implementation of the six §6.2 compilation cases
  (`case_const`, `case_var`, `case_match`, `case_defeasible`,
  `case_sanctions`, `case_fill`), with the lift function `lift_value` and
  an admissibility checker.

The workspace ships 106 tests across the four crates. Benchmarks on Apple
M4 Max (128 GB RAM, Rocq 9.1.1, Criterion 0.5, 30 samples per data point,
1 s warm-up, 3 s measurement window):

- **B1** — `typecheck_program`: 197 ns per step at steady state for N ≥ 16,
  linear in step count.
- **B2** — deterministic execution under `NoopHost`: 370 ns per step.
- **B3** — effect-row composition: 100–125 M steps/sec.
- **B4** — `compile_lex`: 479 ns per admissible Lex term, 2.09 M terms/sec.
- **B5** — proof-bundle size 230 bytes per step; `time coqc` on
  `CompilationSoundness.v` in 0.25 s real from a cold `.vo` cache.

An initial release is tagged. GitHub Actions CI runs Rust and Rocq
pipelines on every push. The workspace compiles standalone from a cold
clone with no path dependencies on sibling checkouts; pinned toolchain at
`rust-toolchain.toml`. The benchmark table above is reproducible with the
commands in `docs/benchmarks.md` §Reproduction.

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
dominance law, typed suspension, local compensation, linear and locked
resources, and session-typed cross-zone execution, as primitive grammar,
with a mechanized soundness pair, a mechanized verdict-preservation
theorem, and a content-addressed replay discipline.

## 10. Open problems

**Remaining Coq obligation.** The `HoleFill (§6.3)` compilation case is
registered as an open theorem in `CompilationSoundness.v`. Strategy:
coinduction on a bisimulation relation pairing each Lex state with the Op
state reached by unwinding one `τ` attestation-append step. The
surrounding inductive definitions are parameterized so a follow-on file
can close the case by mirroring `crates/op-lex-compiler/src/case_fill.rs`.

**Extended metatheory.** Progress, Subject Reduction, and Effect
Monotonicity are stated over the configuration tuple; scaffold
mechanization at `formal/coq/OpCore.v`. Full mechanization of the triple
is open.

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
against the same inputs and pack digest, compares proof bundles digest-by-
digest, and the corridor-translation φ maps the sending-zone verdict into
the receiving-zone compliance lattice. Op is the language layer of Mass;
the proprietary kernel instantiates `OpHost` against compliance packs,
jurisdictional registries, and attestation backends. The open-source Op
tree ships the language surface: syntax, type system, effect system, gas,
evaluator, deterministic lowering, host trait, canonical corpus, and Coq
mechanization.

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
