//! Audit monotonicity — syntactic and semantic.
//!
//! Paper reference: "Op: A Typed Effectful Workflow Language" §5.4
//! "Audit Monotonicity".
//!
//! The audit trail μ is the ordered record of every commit and every
//! compensation the runtime emits. The paper fixes two invariants on μ.
//!
//! 1. **Syntactic monotonicity** — μ is append-only at the byte level.
//!    Once an entry is written, the bytes at that offset never change
//!    and are never removed. A valid observer of μ can rely on earlier
//!    byte ranges being stable even as the program keeps running.
//!
//! 2. **Semantic monotonicity** — a compensation does NOT delete the
//!    forward-commit entry it inverts. Instead, it appends a new entry
//!    of kind `Compensate` that references the inverted entry by index.
//!    The forward commit and its compensation therefore both appear in
//!    μ; the audit trail records the full history, never the net state.
//!
//! These two invariants together imply that replaying μ to any prefix
//! reconstructs the runtime's view of the world at that moment, and
//! that the absence of a compensation entry is load-bearing — a missing
//! compensation cannot be disguised by rewriting the forward commit.

/// A single audit trail entry.
///
/// The entry kind discriminates forward commits from compensations;
/// `references` carries the index of the entry being inverted when
/// `kind == Compensate`, else `None`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct AuditEntry {
    /// 0-based position in the audit trail.
    index: usize,
    /// Entry kind.
    kind: EntryKind,
    /// Step name this entry records.
    step: String,
    /// For `Compensate` entries: the index of the forward commit being
    /// inverted. For `Commit`, `None`.
    references: Option<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum EntryKind {
    /// A forward step committed its effects.
    Commit,
    /// A compensation fired against a prior commit.
    Compensate,
}

/// An append-only audit trail.
///
/// The model mirrors the paper's `μ` exactly: a vector of entries, with
/// a byte-level hash summary so the syntactic-monotonicity test can
/// observe stable prefixes.
#[derive(Debug, Clone, Default)]
struct AuditLog {
    entries: Vec<AuditEntry>,
}

impl AuditLog {
    fn new() -> Self {
        Self::default()
    }

    /// Append a forward commit. Returns the assigned index.
    fn append_commit(&mut self, step: &str) -> usize {
        let index = self.entries.len();
        self.entries.push(AuditEntry {
            index,
            kind: EntryKind::Commit,
            step: step.to_string(),
            references: None,
        });
        index
    }

    /// Append a compensation referencing a prior commit. Returns the
    /// new compensation's index.
    fn append_compensation(&mut self, step: &str, inverts_index: usize) -> usize {
        assert!(
            inverts_index < self.entries.len(),
            "compensation references a nonexistent commit index"
        );
        let index = self.entries.len();
        self.entries.push(AuditEntry {
            index,
            kind: EntryKind::Compensate,
            step: step.to_string(),
            references: Some(inverts_index),
        });
        index
    }

    /// Byte-level snapshot of the trail, used for syntactic-monotonicity
    /// proofs. The format is deterministic: one entry per line, tab
    /// separated, in insertion order.
    fn bytes(&self) -> Vec<u8> {
        let mut out = String::new();
        for e in &self.entries {
            use std::fmt::Write as _;
            match e.kind {
                EntryKind::Commit => {
                    writeln!(&mut out, "{}\tCOMMIT\t{}", e.index, e.step).unwrap();
                }
                EntryKind::Compensate => {
                    let r = e.references.expect("Compensate carries a reference");
                    writeln!(&mut out, "{}\tCOMPENSATE\t{}\t->{}", e.index, e.step, r).unwrap();
                }
            }
        }
        out.into_bytes()
    }
}

#[test]
fn syntactic_monotonicity_prefixes_are_stable() {
    // Build a log step by step. After each append, the bytes written so
    // far must be a prefix of the bytes after the next append. This is
    // the byte-level monotonicity claim: prior bytes never rewritten.
    let mut log = AuditLog::new();
    let mut snapshots: Vec<Vec<u8>> = vec![log.bytes()];

    let c1 = log.append_commit("reserve_seat");
    snapshots.push(log.bytes());
    let c2 = log.append_commit("charge_card");
    snapshots.push(log.bytes());
    // Compensate step 2 first, then step 1 — the reverse-topological
    // order a real compensation runtime uses.
    log.append_compensation("refund_card", c2);
    snapshots.push(log.bytes());
    log.append_compensation("cancel_seat", c1);
    snapshots.push(log.bytes());

    for w in snapshots.windows(2) {
        let prev = &w[0];
        let next = &w[1];
        assert!(
            next.starts_with(prev),
            "byte-level monotonicity violated: prev({} bytes) is not a prefix of next({} bytes)",
            prev.len(),
            next.len()
        );
    }
}

#[test]
fn compensation_appends_without_deleting_forward_commit() {
    // Semantic monotonicity: after a compensation runs, BOTH the forward
    // commit and the compensation entry live in μ. The compensation
    // references the commit by index. The commit entry's byte payload
    // is unchanged — we compare it to its earlier snapshot.
    let mut log = AuditLog::new();

    let commit_index = log.append_commit("book_reservation");
    let after_commit = log.entries[commit_index].clone();

    let comp_index = log.append_compensation("cancel_reservation", commit_index);

    // Forward commit still present at its original position with its
    // original payload — no mutation, no deletion.
    assert_eq!(
        log.entries[commit_index], after_commit,
        "compensation mutated the forward commit it inverts"
    );
    assert_eq!(log.entries[commit_index].kind, EntryKind::Commit);
    assert_eq!(log.entries[commit_index].step, "book_reservation");

    // Compensation is a NEW entry that REFERENCES the commit — not a
    // tombstone sitting on top of the commit.
    assert_eq!(log.entries.len(), 2);
    assert_eq!(log.entries[comp_index].kind, EntryKind::Compensate);
    assert_eq!(log.entries[comp_index].references, Some(commit_index));
    assert_ne!(
        comp_index, commit_index,
        "compensation and commit share an index"
    );
}

#[test]
fn net_state_is_recoverable_but_history_is_preserved() {
    // The paper's semantic point: an observer watching only the NET
    // outcome (commit + compensation = no-op) cannot reconstruct that
    // a commit ever happened. The audit log preserves the history so
    // the observer CAN. This test reifies the claim by counting
    // distinct kinds even when the net state is neutral.
    let mut log = AuditLog::new();
    let c1 = log.append_commit("fiscal_transfer");
    let _cp1 = log.append_compensation("reverse_fiscal_transfer", c1);

    let commits = log
        .entries
        .iter()
        .filter(|e| e.kind == EntryKind::Commit)
        .count();
    let comps = log
        .entries
        .iter()
        .filter(|e| e.kind == EntryKind::Compensate)
        .count();

    assert_eq!(commits, 1, "forward commit must remain in μ");
    assert_eq!(comps, 1, "compensation must be its own entry");
    assert_eq!(
        log.entries.len(),
        commits + comps,
        "no hidden entry kinds"
    );
}

#[test]
fn multiple_compensations_append_in_reverse_topological_order() {
    // Matches the runtime discipline: on failure, the committed prefix
    // is walked back in reverse order; each compensation appends its
    // own entry referencing the corresponding commit. The final trail
    // is [C1, C2, C3, Comp3, Comp2, Comp1].
    let mut log = AuditLog::new();
    let c1 = log.append_commit("step_1");
    let c2 = log.append_commit("step_2");
    let c3 = log.append_commit("step_3");

    // Reverse-topological compensation.
    log.append_compensation("inv_3", c3);
    log.append_compensation("inv_2", c2);
    log.append_compensation("inv_1", c1);

    let kinds: Vec<_> = log.entries.iter().map(|e| (&e.kind, e.step.as_str())).collect();
    assert_eq!(
        kinds,
        vec![
            (&EntryKind::Commit, "step_1"),
            (&EntryKind::Commit, "step_2"),
            (&EntryKind::Commit, "step_3"),
            (&EntryKind::Compensate, "inv_3"),
            (&EntryKind::Compensate, "inv_2"),
            (&EntryKind::Compensate, "inv_1"),
        ],
    );

    // Every compensation references an earlier index — reverse
    // topological ordering means each `references` must be strictly
    // less than the compensation's own index.
    for e in &log.entries {
        if let Some(r) = e.references {
            assert!(
                r < e.index,
                "compensation at {} references a later index {}",
                e.index,
                r
            );
        }
    }
}
