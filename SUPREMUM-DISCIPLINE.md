# Supremum Discipline

Use this reference for architectural and research decisions within the assigned
scope. Preserve the strongest defensible target. State its current evidence and
remaining obligations separately.

## Decision rule

A candidate is admissible when it preserves safety, license correctness,
public-source hygiene, proof honesty, auditability, and reproducibility.
Repository contributions remain Apache-2.0. Dependency licenses follow the
repository contract. Private source dependencies remain outside this public tree.

Define the load-bearing comparison dimensions for the decision. These can
include guarantees, coverage, isolation, performance, and operator independence.
For admissible candidates, write `A <= B` when B is at least as strong as A on
every stated dimension. A supremum is a least upper bound when one exists.
A maximal candidate has no strictly stronger admissible candidate in that order.
Do not assume either exists without establishing it for the candidate set.

Compare the relevant alternatives. When compatible alternatives can be combined
within scope, check the combined design and its consistency obligations. When
alternatives conflict, prefer safety and proof guarantees, then auditability and
operator independence. Record an unresolved conflict rather than claiming a
unique optimum.

## Execution and evidence

Specify the intended outcome before choosing implementation steps. Preserve
that outcome through necessary sequencing. Do not silently replace it with a
weaker target because the weaker target is easier to test.

Use actual tool availability, resources, dependencies, and authorized budgets.
Choose verification methods that establish the affected guarantees. Multiple
proof systems or providers are required when the specification or threat model
requires them. Their number alone does not establish independence or correctness.

A bounded investigation can finish with a proof, a counterexample, or an exact
unresolved obligation supported by the work performed. Record attempted routes
and the next discriminating step for an unresolved result. This closes the
investigation only. It does not close the theorem or implementation objective.

For implementation, continue authorized work until acceptance evidence establishes
the requested outcome or a concrete blocker prevents further progress. Preserve
unfinished obligations and report their scope. Keep conjecture, scaffold,
implementation, test evidence, and closed proof distinct.

## Ownership

Apply this decision rule within the assigned repository and task. Loading it
does not authorize writes to companions, new standing goals, deployment, or
publication. Update the paired `AGENTS.md` and `CLAUDE.md` when the local
contract changes. Report dependent work outside the assignment to its owner.
