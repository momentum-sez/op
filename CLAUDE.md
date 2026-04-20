# CLAUDE.md — Op

<!-- BEGIN ALWAYS-DEEP-SEMANTIC-MERGE (canonical rule — do not remove or edit) -->

## NON-NEGOTIABLE: Always do deep semantic merges — never rewrite

When merging work from another branch, worktree, or agent output into a
trunk branch: ALWAYS do a deep semantic merge by reviewing each diff
hunk and deciding per-hunk whether target wins, source wins, or both
pieces need to be preserved. NEVER do a wholesale file copy. NEVER
`-s ours`/`-s theirs` as a shortcut. NEVER "one side wins entirely"
when both sides have modified a file.

For every merge from a non-ancestor branch:
1. `git diff <target> <source> -- <path>` per file; read every hunk.
2. Per hunk, decide: target wins / source wins / compose both.
3. For whole-file divergence, write a unified version; don't pick one.
4. If genuinely incompatible, STOP and ask the user.
5. `cp` + commit is valid ONLY for files that exist on one side only.
6. `-s ours` is valid ONLY when source content is already absorbed.

Violation destroys real engineering work silently and irrecoverably.

<!-- END ALWAYS-DEEP-SEMANTIC-MERGE -->

<!-- BEGIN NO-DESTRUCTIVE-GIT (canonical rule — do not remove or edit) -->

## NON-NEGOTIABLE: No destructive git — ever

Applies across every Mass / Momentum / Moxie repo
(moxie, moxie-whitepaper, moxie/web, kernel, kernel worktrees, centcom, stack, lex, op,
gstore, momentum, momentum-dev, momentum-research, momentum-docs, mass-webapp,
mass-bom, api-gateway, attestation-engine, templating-engine, starters,
organization-info, investment-info, treasury-info, identity-info, consent-info,
governance-info, institutional-world-model-whitepaper,
programmable-institutions-whitepaper, and every other Mass/Momentum/Moxie repo).

**Forbidden commands (non-exhaustive):**

- `git commit` from a subagent (main thread commits only — subagents stage only)
- `git push` in any form, any branch (main thread pushes only)
- `git reset --hard`, `git reset --keep`, or any `git reset` that moves HEAD
- `git checkout` of a shared checkout, `git switch`, `git restore`
- `git stash` in any form (including `pop`, `drop`, `apply`, `clear`)
- `git clean` in any form (`-f`, `-fd`, `-x`, …)
- `git rebase` in any form (including interactive)
- `git branch -D`, `git branch --delete --force`
- `git worktree remove --force`
- `git update-ref`, `git filter-branch`, `git filter-repo`
- `rm -rf` on anything git-tracked

**Required:**

- Agents stage changes only (`git add <path>`). The main thread alone commits and pushes.
- Parallel work uses `git worktree add <unique-path> -b <unique-branch> origin/<base>` and operates inside that isolated path. Never mutate the shared checkout's HEAD.
- Merge conflicts are resolved via merge commits — never via `reset`, `stash`, or `checkout`.
- If a destructive op seems necessary, STOP and escalate to the user. Do not proceed.

**Additive alternatives (always safe):** `git worktree add`, `git revert <commit>`,
`git diff > patch.diff`, `git merge` (no-ff or default), `git fetch`.

This rule survives context compression. Every agent spawned in this repo inherits it.

**Incident reference:** 2026-04-16, Agent 5 (conservation invariants) ran
`git reset --hard --no-recurse-submodules` inside its isolated worktree despite a
"DO NOT commit. Stage only." instruction. The prompt failed to enumerate the
forbidden-command list verbatim. Lesson: the list above must be pasted into every
agent prompt — no paraphrasing, no abbreviation.

<!-- END NO-DESTRUCTIVE-GIT -->

<!-- BEGIN MULTI-AGENT-CONCURRENCY (canonical rule — do not remove or edit) -->

## NON-NEGOTIABLE: Multi-agent concurrency via worktrees

Many local agents run against this repo simultaneously from a single main thread.
They MUST share the repo without destructive interaction. The only safe model:

**Every non-trivial agent operates in its own git worktree:**

```
git worktree add <unique-path> -b <unique-branch> origin/<base-branch>
cd <unique-path>
# ... do work, stage changes ...
# main thread reviews, merges (merge commit only), pushes
```

- `<unique-path>` must be unique per agent (e.g. `/tmp/agent-<id>` or a path that embeds a UUID/task-id). Never reuse paths across agents.
- `<unique-branch>` must be unique per agent (e.g. `agent/<task-id>` or `frontier/<name>-<short-sha>`). Never reuse branch names.
- `<base-branch>` is whatever the user has checked out on main thread (typically `develop` or `main`).

**Rules for concurrent agents:**

1. An agent operates ONLY inside its own worktree path. Never `cd` out of it into the shared checkout. Never read/write files in the shared checkout (that path belongs to the main thread and possibly other agents).
2. An agent never touches HEAD of the shared checkout. No `git checkout`, `git switch`, `git reset`, `git rebase` anywhere.
3. An agent never mutates another agent's worktree or branch.
4. An agent stages changes inside its worktree (`git add`). It does NOT commit. The main thread commits after reviewing the staged changes (agents cannot reliably write good commit messages under a shared history, and commits from parallel agents race on the branch ref).
5. An agent never pushes. Only the main thread pushes.
6. When an agent finishes, its worktree and branch stay until the main thread merges or the user explicitly authorizes cleanup. Do NOT `git worktree remove` your own worktree on exit — the harness cleans up when appropriate.
7. If an agent hits a conflict with another agent's work, it reports the conflict to the main thread and stops. It does NOT resolve the conflict via reset/checkout/stash.
8. If an agent needs to read another repo (cross-repo context), it reads files directly (Read tool) — it does NOT `git checkout` or `git worktree add` in a repo it is not assigned to.

**Read-only agents** (audit, explore, documentation search) may operate in the shared checkout without worktree isolation, because they do not write. They still never run any git command that mutates state.

**File-locking guidance for agents sharing the main checkout (read-only only):**

- Use Read, Grep, Glob freely.
- Do NOT use Edit, Write, or Bash commands that write files in the shared checkout.
- If you find something that needs a write, report it — don't write.

**If any of the above becomes infeasible, STOP and escalate to the user.**
Never silently break the concurrency invariant.

<!-- END MULTI-AGENT-CONCURRENCY -->

Op: typed effectful workflow language for multi-step economic programs.
Step composition is explicit, steps have typed I/O, effects are tracked
statically, compensation attaches to the forward program it inverts, and
proof obligations are first-class constructs.

**Paper:** "Op: A Typed Effectful Workflow Language" — research.momentum.inc

## Repository Structure

```
op/
├── crates/
│   ├── op-core/       # Language core: AST, types, effects, gas, evaluator
│   │   ├── src/
│   │   │   ├── ast.rs        # Program, Step, Expr, Type
│   │   │   ├── effects.rs    # Effect row algebra, effect safety rules
│   │   │   ├── types.rs      # Bidirectional type checker, linearity tracking
│   │   │   ├── gas.rs        # Two-tier gas (structural + extensional)
│   │   │   ├── parser.rs     # JSON wire-format parser (round-trip with AST serde)
│   │   │   ├── evaluator.rs  # Deterministic evaluator, host-abstraction trait
│   │   │   ├── host.rs       # Host primitive trait
│   │   │   ├── error.rs      # OpError variants
│   │   │   └── lib.rs        # Public re-exports
│   │   └── tests/
│   ├── op-compiler/   # Source-language / YAML → Op AST lowering
│   │   └── src/
│   │       ├── lower.rs      # YAML OperationDefinition → Op program
│   │       ├── hash.rs       # FNV-1a content addressing
│   │       └── lib.rs
│   └── op-stdlib/     # Canonical operation corpus and host trait scaffold
│       └── src/
│           ├── canonical.rs  # Entity, Ownership, Fiscal, Identity, Consent primitives
│           └── lib.rs
├── docs/
│   └── language-spec.md      # Canonical language reference
├── examples/
│   └── hello-op.rs           # Minimum-viable embedding
├── formal/
│   ├── coq/                  # Coq scaffolds (placeholder)
│   ├── lean/                 # Lean scaffolds (placeholder)
│   └── README.md
├── Cargo.toml
├── CLAUDE.md
├── LICENSE
└── README.md
```

## Key Design Properties

1. **Typed step signatures** — `step s : In -> Out ! E` makes composition explicit;
   mismatched upstream outputs fail to type-check.
2. **Effect rows** — path-indexed, decomposed by primitive family; `sovereign_write`
   must be dominated by `sanctions_check` except for the deferred-subject case of
   entity creation.
3. **Typed await** — `Await<Event, Payload>` distinguishes waiting from completion at
   the type level, mirroring the operational distinction.
4. **Local compensation** — `compensate { ... }` attaches to the step it inverts; the
   compiler derives the reverse-topological rollback plan.
5. **Linear resources** — `Linear<T>` single-use, `Locked<T>` two-eliminator (commit or
   release), `Affine` consumable. Linearity violations surface at type-check.
6. **Two-tier gas** — structural gas bounded statically by program shape, extensional
   gas metered against cardinality certificates at runtime.
7. **Deterministic lowering** — Op programs lower deterministically into a runtime
   execution plan. Legacy YAML can be imported through the same plan structure.

## Host Abstraction

Op is a language and VM. Host primitives (compliance packs, proof systems,
attestation backends, jurisdictional registries) plug in through `op_core::host::OpHost`.
The same Op program can be executed against different sovereign execution
contexts by supplying a different `OpHost` implementation.

The canonical operation corpus (`op_stdlib::canonical`) describes the shape of
each primitive family (entity create, fiscal transfer, sanctions screening,
document generation, governance request, registry filing) without binding a
specific backend. Embedders register concrete implementations against the
corpus identifiers.

## Relation to mez-op inside ~/kernel

The Mass kernel (private tree under `~/kernel`) carries `mez-op*` crates that
instantiate Op against the kernel's proprietary compliance, pack, tensor, and
corpus types. This OSS tree ships only the language layer: syntax, type system,
effect system, gas, evaluator, deterministic lowering, host trait, and canonical
corpus. Host bindings for the kernel remain in `~/kernel` and are not part of
this repository.

Op's public surface is stable at the AST, type, effect, and host-trait
boundaries. Breaking changes to any of these require a major version bump.

## Test Suite

The workspace ships unit tests per module plus integration tests exercising
end-to-end compilation of the canonical corpus.

```bash
cargo test --workspace
```

## Build

```bash
cargo check --workspace
cargo test --workspace
cargo clippy --workspace -- -D warnings
```

The workspace has no path dependencies on external checkouts. It compiles
standalone from a cold clone.

## License

Apache-2.0. Op is a contribution to the study of typed workflow languages for
institutional computation — not a proprietary implementation detail. Published
as part of the Momentum research programme at research.momentum.inc.

## Git Commit Rules

- **No LLM credit in git commits.** NEVER include `Co-Authored-By` lines
  referencing Claude, Opus, GPT, Codex, or any LLM in commit messages. The
  author is the human operator.
