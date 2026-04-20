# Supremum Discipline

At every architectural, design, research, synthesis, or implementation decision point, pick the **supremum**: the hardest, most complete, best-guaranteed, most-verified, most-scalable, most-performant option available.

**Cost, time, and talent are not constraints.** Treat resources as infinite. No "practical" compromises, no deferred tiers, no sequenced migrations, no choosing one of two when both can be shipped simultaneously.

This applies across every Mass, Momentum, Moxie, centcom, kernel, stack, lex, op, gstore, and adjacent repo. The principal's standing instruction.

## How to apply

At every binary or n-ary decision point:

1. **List all options.** Don't prune on "practicality" before enumerating.
2. **Identify the supremum option** — the one with the strongest guarantee, most complete coverage, widest applicability, most formal verification, most redundancy, most isolation, most defense-in-depth.
3. **Pick the supremum.** If it requires more resources / time / talent, that is not a reason to compromise.
4. **Where two options are complementary** (e.g., corridor-param AND 24th-domain, both surfaces of the same primitive), ship BOTH simultaneously with an explicit cross-consistency invariant — not one or the other.
5. **Where options are sequenced** (stage C → B → A), question the sequencing premise. Default to shipping the terminal stage at T=0.
6. **Where candidates are "deferred"**, commit them as first-class now. Deferral is a form of compromise.
7. **Where residuals are identified**, publish an explicit research program toward closure. Residuals are NOT acceptable as permanent state.
8. **Where "N-vendor" is specified**, pick N ≥ 3 (or the highest defensible N). Multi-vendor ≥ 5 for hardware substrates. No single-vendor operational paths.
9. **Where a termination layer is needed** (e.g., recursive attack chain), pick mechanized formal-verification-bounded proof over honest-residuals documentation. Mechanize in Coq + Lean + Rust — not pick-one.
10. **Apply to every artifact** — code, docs, architecture, roadmap, research. The discipline is universal, not domain-specific.

## Examples of supremum calls vs non-supremum calls

| Decision | Non-supremum | Supremum |
|---|---|---|
| Commitment scope | 14 commitments + 1 candidate deferred | 19 commitments, all first-class |
| Substrate isolation | 2-tier model (compliance + SCM) | Per-domain substrate (23 MPC quorums per tier) |
| Migration path | Stage C MVP → Stage B hybrid → Stage A terminal | Stage A at T=0 |
| Multi-vendor redundancy | Single-vendor or N=2 | N ≥ 3 with divergence attestation; ≥ 5 for hardware roots |
| Formal verification | Tier-A + Tier-B; Tier-C deferred | Full Tier-A + Tier-B + Tier-C + Tier-D, all mechanized |
| Regress termination | Honest residuals documentation | Formal-verification-bounded ZK-proof of meta-protocol soundness |
| Two complementary placements | Pick one (corridor-param OR 24th-domain) | Ship both with cross-consistency invariant |
| Residual attack classes | Accept + document | Publish explicit closure research program per class |

## Scope

Universal across every Mass / Momentum / Moxie / centcom / kernel / stack / lex / op / gstore / whitepaper / service repo. Applies to code, design docs, architecture decisions, roadmap phases, research waves, synthesis documents, and deal materials.

**Anchor.** `~/.claude/projects/-Users-raeez-centcom/memory/feedback_supremum_discipline.md` is the persistent feedback memory entry. This per-repo file is the visible surface so every engineer and agent encounters the discipline when touching any codebase.

**Do not compromise on the supremum. Cost, time, and talent are not constraints.**
