# CLAUDE.md — op

> **This public repository carries its agent rules inline.** The block below is a public-safe export of the project-wide operating discipline, so external clones are self-contained and do not depend on private paths or internal repositories.

---

This public repository carries shared agent rules inline. Local rules follow.
The paired instruction files have the same repository contract.

<!-- BEGIN INLINED-INVARIANTS (public-safe export from ecosystem invariants) -->

## I. No Destructive Git

Do not discard, rewrite, or hide work. The following commands are forbidden:

- `git commit` from a subagent (main thread commits only — subagents stage only)
- `git push` in any form, any branch (main thread pushes only)
- `git reset` in any form, including path-only / index-only resets
- `git checkout`, `git switch`, `git restore` in any form
- `git commit --amend`
- `git stash` in any form (including `pop`, `drop`, `apply`, `clear`)
- `git clean` in any form (`-f`, `-fd`, `-x`, …)
- `git rebase` in any form (including interactive)
- `git branch -D`, `git branch --delete --force`
- `git worktree remove` or `git worktree prune` unless the principal explicitly authorizes cleanup
- `git update-ref`, `git filter-branch`, `git filter-repo`
- `rm -rf` on anything git-tracked
- `--no-verify`, `--no-gpg-sign` on commits unless the principal explicitly requests

Main-thread commits and publication require user authorization. If a forbidden operation appears necessary, stop and report the blocker.

## II. Multi-Agent Concurrency

Read-only agents may inspect a shared checkout. Write-capable parallel agents must use isolated worktrees with explicit ownership, unique branch names, and clear verification commands. Agents do not commit, push, clean up worktrees, or mutate another agent's files.

## III. Public Documents Stand Alone

External-facing documents must make sense to a cold reader. Remove private paths, private repository names, internal process labels, draft/version chatter, and unsupported claims. State the present mathematical or engineering object and its exact proof or verification status.

## IV. Technical English and Research Voice

All maintained English technical prose must follow ASD-STE100 Simplified Technical English, Issue 9.

- Use approved general words and registered technical terms.
- Define each term before use.
- Use active voice.
- Use one topic in each paragraph.
- Use no more than 20 words in a procedural sentence.
- Use no more than 25 words in a descriptive sentence.
- Do not use contractions or semicolons.
- Code, identifiers, formulas, quotations, citations, and mandated text are not prose.
- Apply this rule to the surrounding explanations.
- Formal research can use accepted subject terms. This rule still controls its English sentence structure.

## V. Artifact Hygiene

Material that informs the repository should live in the repository or in a referenced public source. Do not rely on ephemeral local downloads or private-only artifacts for public claims.

## VI. No Tool Attribution In Persistent Artifacts

Commits, changelogs, generated headers, PR descriptions, and published documents must not attribute authorship to an AI model, assistant, or automation harness. The human maintainer is the project author of record.

## VII. Deep Semantic Merges

When integrating another branch or generated patch, read each changed hunk and preserve the correct semantics. Do not choose one side wholesale when both contain relevant work.

## VIII. Intelligence Propagation

When a new fact changes a downstream claim, update affected documents, tests, and examples within the authorized paths. For unassigned repositories, record the affected artifact, evidence, required change, and next owner. A request to read or open an artifact requires a freshness assessment, not automatic reconstruction. Preparation does not authorize publication.

## IX. Scope Discipline

Keep edits inside the requested surface. Avoid unrelated refactors. If a claim cannot be proved or tested within scope, record it as a residual obligation instead of presenting it as complete.

## X. Mathematical Repair Doctrine

If a proof, theorem, formal scaffold, executable semantics claim, or paper claim breaks, repair the object. Do not converge by deleting, demoting, or quietly weakening it. If repair cannot be completed, name the exact obstruction and next proof obligation.

## XI. Code-Writing Discipline

Nineteen rules govern code-writing work. Apply judgment in proportion to risk.

**Rule 1 — Think Before Coding.** Inspect evidence and state material assumptions. Resolve routine uncertainty within the authorized scope. Ask when unresolved uncertainty changes authority, correctness, or an irreversible action.

**Rule 2 — Simplicity First.** Minimum code that solves the problem. Nothing speculative. No features beyond what was asked. No abstractions for single-use code. Test: would a senior engineer say this is overcomplicated? If yes, simplify.

**Rule 3 — Surgical Changes.** Touch only what you must. Clean up only your own mess. Don't "improve" adjacent code, comments, or formatting. Don't refactor what isn't broken. Match existing style.

**Rule 4 — Goal-Driven Execution.** Define success criteria. Loop until verified. Don't follow steps; define success and iterate. Strong success criteria let you loop independently.

**Rule 5 — Use the model only for judgment calls.** Use the model for classification, drafting, summarization, extraction. Do NOT use the model for routing, retries, deterministic transforms. If code can answer, code answers.

**Rule 6 — Respect explicit resource limits.** Honor explicit user or host budgets. Do not invent per-task or per-session token caps. Checkpoint verified work and remaining obligations when context is constrained. Continue authorized work while meaningful progress is possible.

**Rule 7 — Surface conflicts, don't average them.** If two patterns contradict, pick one (more recent / more tested). Explain why. Flag the other for cleanup. Don't blend conflicting patterns.

**Rule 8 — Read before you write.** Read the relevant exports, callers, and shared utilities. Investigate uncertain structure before changing it.

**Rule 9 — Tests verify intent, not just behaviour.** Tests must encode WHY behaviour matters, not just WHAT it does. A test that can't fail when business logic changes is wrong.

**Rule 10 — Checkpoint after every significant step.** Summarize what was done, what's verified, what's left. Don't continue from a state you can't describe back. If you lose track, stop and restate.

**Rule 11 — Match the codebase's conventions, even if you disagree.** Conformance > taste inside the codebase. If you genuinely think a convention is harmful, surface it. Don't fork silently.

**Rule 12 — Fail loud.** "Completed" is wrong if anything was skipped silently. "Tests pass" is wrong if any were skipped. Default to surfacing uncertainty, not hiding it.

**Rule 13 — No backward compatibility.** Do not preserve backward compatibility. Remove obsolete paths instead of adding compatibility layers, fallbacks, or migrations.

**Rule 14 — Simplest implementation that fully meets the requirements.** Choose the simplest implementation that fully meets the current requirements. Avoid speculative abstractions, configuration, and indirection.

**Rule 15 — Grow the system in layers.** Start from the smallest version that works end to end, and add each new capability on top of a product that already works. Never trade a working product for unfinished complexity.

**Rule 16 — Modular components, separated concerns.** Keep components modular and concerns clearly separated.

**Rule 17 — Prefer established libraries.** Prefer established, well-maintained libraries when they reduce overall complexity or improve reliability. Do not reimplement common functionality without a clear reason.

**Rule 18 — Lean on the dependencies already present.** Lean on the dependencies already in the project before writing your own implementation or adding packages. Do not assume a library lacks a capability without checking its documentation and types.

**Rule 19 — Architectural decisions for the long term.** Make architectural decisions for the long term. Do not accept a stopgap that only works for now and is meant to be replaced later.

**Boundaries.** Rule 13 is an edit, never a git-history operation: the No Destructive Git rule stands, and the deleted path lives in history. Rule 13 deletes code paths, flags, shims, and dead branches; doctrine, documents, and canonical numbers still retire to `archive/` or `deprecated/` under the repository retention policy. Rule 13 stops at a relied-upon external boundary — a wire object, a published API contract, an executed instrument, or a schema a deployed node depends on changes by a versioned protocol decision, not by cleanup. Rule 14 governs the amount of machinery and Rule 19 governs the shape of the boundary; a small implementation behind a correct boundary satisfies both, and neither licenses a stopgap. Rules 17 and 18 yield to the open-source whitelist and licence review before any new dependency enters a public repository.

<!-- END INLINED-INVARIANTS -->

## Repository contract

Keep `AGENTS.md` and `CLAUDE.md` consistent on repository facts. Before code edits,
read `CLAUDE.md` and any closer instruction file for the affected directory.
Use the local source and tests to resolve factual drift. Read
`SUPREMUM-DISCIPLINE.md` for architectural or research choices when present.

Keep changes within assigned files and repositories. Update affected references
within that scope. Report downstream work to its owner. Local verification does
not authorize deployment, signing, sending, committing, or publication.

Public artifacts must remain usable from an external clone. Cite public sources
and local paths. Keep proprietary content and private repository identities out.
Repository contributions use Apache-2.0. Preserve dependency license notices.

Distinguish implemented behavior, tested examples, formal scaffolds, proved
statements, conjectures, and open obligations. Preserve theorem hypotheses and
proof rigor. Report the exact remaining obligation when an investigation ends
without a proof. Never claim a build or scaffold proves the full system.

## Integration branch and worktree discipline

The integration branch is `develop`. Release branches change only by
maintainer decision. Each write-capable agent works in its own worktree on a
unique branch cut from the integration head. Subagents stage only. The main
thread reviews, commits, and pushes. A session can end without warning. Write
verified state and open obligations into a record in the worktree as work
proceeds, and resume from that record. Commits carry no model or tool
attribution.

## System role

Lex supplies jurisdictional rule logic. Op carries compliance obligations in
executable operations. gstore keeps Merkle-authenticated state. Moxie prices
and clears claims and their derivatives. Mass operates the legal entity behind
a claim end to end. Recourse administers cases, authority records, outcomes,
stays, execution coordination, and recovery. This repository owns the Op layer only.

## Purpose and routing

Op is a typed, stack-based bytecode with deterministic operational semantics
for compliance-carrying operations (`README.md`). It provides syntax, types,
effects, gas analysis, deterministic lowering, host interfaces, and a primitive
corpus. Lex, the jurisdictional rule language, compiles into Op.
Public companions are `github.com/momentum-sez/lex`,
`github.com/momentum-sez/gstore`, and `github.com/momentum-sez/stack`.

| Task | Read |
| --- | --- |
| AST, type checker, effects, gas, parser | `crates/op-core/src/` |
| Host contract | `crates/op-core/src/host.rs` |
| YAML lowering | `crates/op-compiler/src/lower.rs` |
| Primitive corpus | `crates/op-stdlib/src/canonical.rs` |
| Lex compilation and reference interpretation | `crates/op-lex-compiler/src/`, especially `interp.rs` |
| Minimum embedding example | `crates/op-core/examples/hello-op.rs` |
| Public language contract | `docs/language-spec.md` |
| Formal proof scope | `formal/README.md`, `formal/coq/`, `formal/lean/` |

Host implementations live in the embedder's repository. Keep the language
surface independent of proprietary backend code. Public AST, type, effect, and
host-trait breaking changes require a major version bump coordinated with the
maintainer.

## Semantic boundaries

Name the affected typing, effect, linearity, compensation, gas, host, or compiler
invariant before changing it. Inspect implementations and affected tests. Preserve
sanctions-dominance rules and the documented deferred-subject creation case.
Distinguish static gas bounds from runtime charging. Confirm actual evaluator
integration before claiming enforcement during execution.

For Lex-to-Op work, inspect the checked compiler domain, admission contract, and
proof scope. Toy-fragment soundness and adequacy skeletons do not establish
soundness for the full Op AST. Preserve closed lemmas and identify assumptions
and open obligations precisely.

## Verification

Run commands from the repository root:

```bash
cargo fmt --all -- --check
cargo check --workspace --all-targets
cargo test --workspace --all-targets
cargo clippy --workspace --all-targets -- -D warnings
cargo run -p op-core --example hello-op
```

These commands match `.github/workflows/ci.yml`. The `forbidden-strings`,
`cold-clone`, and `coq` workflows run on pushes to `main`, `master`, and
`develop`, and on pull requests.

Start with the affected crate or example. Broaden to the workspace for shared
contracts or compiler changes. Formal edits follow the current project build
instructions and configuration under `formal/`. Check the relevant proof
assumptions in addition to compilation. End-to-end compilation and adversarial
semantic tests verify different properties. Use each where the change needs it.
