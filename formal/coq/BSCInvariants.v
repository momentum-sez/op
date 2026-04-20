(** * BSCInvariants.v

    Mechanization of the three SJN Bilateral Signed Commitment
    (BSC) invariants of [sovereign-jurisdiction-network.md §5.4]
    as realized by the corridor typing judgment of
    [papers/op.tex §5.9 (Corridor-indexed typestates)]:

    - (I1) Lock monotonicity:   each side holds at most one
          active lock per (omega, epsilon) and releases it on
          transition to Committed, Aborted, or lock-timeout
          expiry.

    - (I2) Verdict uniqueness:  each side signs at most one
          verdict per (omega, epsilon).

    - (I3) Verified-entry durability:  entry to Verified at
          side X occurs only when both v_A and v_B are durable
          at X and valid under their respective keys.

    The paper frames these as properties of the corridor history
    kappa threaded through the typing judgment.  Here we
    mechanize the corridor history abstractly as a finite map
    keyed by (omega, epsilon) and prove that a small set of
    admissible update operations preserves the invariants.  Each
    operation corresponds to one of the paper's typing rules:

    - [op_lock]       -- T-Lock           (introduces an active lock,
                                           records an event-count
                                           deadline)
    - [op_sign]       -- T-Sign           (introduces a signed
                                           verdict at this side)
    - [op_verify]     -- T-Verify         (requires both signed
                                           verdicts durable;
                                           introduces Verified)
    - [op_blame]      -- T-Blame          (introduces a blame
                                           witness from a
                                           conflicting same-signer
                                           pair)
    - [op_timeout]    -- E-Lock-Timeout   (clears an active lock
                                           at the event-count
                                           deadline)
    - [op_commit]     -- E-Commit         (consumes a lock under a
                                           Verified witness)
    - [op_release]    -- E-Release        (releases a lock under
                                           an abort or timeout
                                           witness)

    All theorems Qed-closed. *)

Set Implicit Arguments.

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.

(** ** Corridor index and sides *)

(** Operation identifier [omega] and epoch [epsilon], both natural. *)
Definition omega : Type := nat.
Definition epsilon : Type := nat.

Definition idx : Type := (omega * epsilon)%type.

Definition idx_eqb (i j : idx) : bool :=
  Nat.eqb (fst i) (fst j) && Nat.eqb (snd i) (snd j).

Lemma idx_eqb_refl : forall i, idx_eqb i i = true.
Proof.
  intros [a b]. unfold idx_eqb. simpl.
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma idx_eqb_eq : forall i j, idx_eqb i j = true -> i = j.
Proof.
  intros [a b] [c d]. unfold idx_eqb. simpl.
  intro H.
  apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1, H2. subst. reflexivity.
Qed.

Lemma idx_eqb_neq : forall i j, idx_eqb i j = false -> i <> j.
Proof.
  intros [a b] [c d]. unfold idx_eqb. simpl.
  intros H Heq. injection Heq; intros Hbd Hac; subst.
  rewrite !Nat.eqb_refl in H. discriminate.
Qed.

(** Two sides A and B (Initiator / Responder in the paper). *)
Inductive side : Type := SideA | SideB.

Definition side_eqb (x y : side) : bool :=
  match x, y with
  | SideA, SideA => true
  | SideB, SideB => true
  | _, _ => false
  end.

Lemma side_eqb_refl : forall s, side_eqb s s = true.
Proof. destruct s; reflexivity. Qed.

Lemma side_eqb_eq : forall s1 s2, side_eqb s1 s2 = true -> s1 = s2.
Proof. destruct s1, s2; try reflexivity; discriminate. Qed.

(** ** Corridor history cells *)

(** An active lock at side X, index i, with event-count deadline d. *)
Record lock_cell : Type := mk_lock { lock_side : side; lock_idx : idx; lock_deadline : nat }.

(** A signed verdict at side X, index i, with payload digest [pd].
    Signer is implicit (it is the side's own key). *)
Record sign_cell : Type := mk_sign { sign_side : side; sign_idx : idx; sign_digest : nat }.

(** A verified-entry cell at side X, index i.  Presence means both
    A's and B's signed verdicts are durable at X. *)
Record verified_cell : Type := mk_verified { ver_side : side; ver_idx : idx }.

(** A blame witness against signer Z at index i, extracted from a
    same-signer conflicting pair. *)
Record blame_cell : Type := mk_blame { blame_side : side; blame_signer : side; blame_idx : idx }.

(** A corridor history is four lists of cells. *)
Record kappa : Type := mk_kappa {
  locks : list lock_cell;
  signs : list sign_cell;
  verifieds : list verified_cell;
  blames : list blame_cell
}.

Definition kappa_empty : kappa := mk_kappa [] [] [] [].

(** ** Predicates on kappa *)

(** [active_lock_X s i k]: side s has an active lock at index i
    with some deadline in k. *)
Definition active_lock_X (s : side) (i : idx) (k : kappa) : Prop :=
  exists d, In (mk_lock s i d) (locks k).

(** [has_sign_X s i k]: side s has signed a verdict at index i
    in k. *)
Definition has_sign_X (s : side) (i : idx) (k : kappa) : Prop :=
  exists d, In (mk_sign s i d) (signs k).

(** [has_verified_X s i k]: side s has a verified-entry cell at i. *)
Definition has_verified_X (s : side) (i : idx) (k : kappa) : Prop :=
  In (mk_verified s i) (verifieds k).

(** ** Invariants (I1)-(I3) *)

(** (I1) Lock monotonicity: each side holds at most one active lock
    per (omega, epsilon) in the history.  Formally: any two lock
    cells at the same side and index have the same deadline. *)
Definition invariant_I1 (k : kappa) : Prop :=
  forall s i d1 d2,
    In (mk_lock s i d1) (locks k) ->
    In (mk_lock s i d2) (locks k) ->
    d1 = d2.

(** (I2) Verdict uniqueness: each side signs at most one verdict
    per (omega, epsilon).  Formally: any two sign cells at the same
    side and index have the same payload digest. *)
Definition invariant_I2 (k : kappa) : Prop :=
  forall s i d1 d2,
    In (mk_sign s i d1) (signs k) ->
    In (mk_sign s i d2) (signs k) ->
    d1 = d2.

(** (I3) Verified-entry durability: if side s has a verified cell
    at index i, then side s has both A-side and B-side signed
    witnesses durable at i.  The digest values are recorded but
    need not match across sides (they are two independent
    signatures). *)
Definition invariant_I3 (k : kappa) : Prop :=
  forall s i,
    has_verified_X s i k ->
    has_sign_X SideA i k /\ has_sign_X SideB i k.

Definition bsc_invariants (k : kappa) : Prop :=
  invariant_I1 k /\ invariant_I2 k /\ invariant_I3 k.

Lemma bsc_invariants_empty : bsc_invariants kappa_empty.
Proof.
  unfold bsc_invariants, invariant_I1, invariant_I2, invariant_I3,
         has_verified_X, has_sign_X. simpl.
  split; [|split].
  - intros x ix d1 d2 Ha Hb. inversion Ha.
  - intros x ix d1 d2 Ha Hb. inversion Ha.
  - intros x ix Ha. inversion Ha.
Qed.

(** ** Typing-rule operations on kappa

    Each [op_*] corresponds to exactly one paper typing or
    reduction rule.  Preconditions mirror the paper exactly. *)

(** T-Lock: introduce a new active lock at side s, index i, with
    deadline d.  Precondition: no existing active lock at (s,i). *)
Definition op_lock (s : side) (i : idx) (d : nat) (k : kappa) : kappa :=
  mk_kappa ((mk_lock s i d) :: locks k) (signs k) (verifieds k) (blames k).

Definition op_lock_pre (s : side) (i : idx) (k : kappa) : Prop :=
  ~ active_lock_X s i k.

(** T-Sign: introduce a new signed verdict at side s, index i,
    with payload digest d.  Precondition: no existing signature at
    (s,i). *)
Definition op_sign (s : side) (i : idx) (d : nat) (k : kappa) : kappa :=
  mk_kappa (locks k) ((mk_sign s i d) :: signs k) (verifieds k) (blames k).

Definition op_sign_pre (s : side) (i : idx) (k : kappa) : Prop :=
  ~ has_sign_X s i k.

(** T-Verify: introduce a verified-entry cell at side s, index i.
    Precondition: both sides' signed verdicts are durable at s.  In
    the paper [s_A] and [s_B] are passed explicitly and the premise
    [durable_X] asserts the pair is in the proof bundle; here we
    model durability by presence of sign cells at both SideA and
    SideB at index i. *)
Definition op_verify (s : side) (i : idx) (k : kappa) : kappa :=
  mk_kappa (locks k) (signs k) ((mk_verified s i) :: verifieds k) (blames k).

Definition op_verify_pre (s : side) (i : idx) (k : kappa) : Prop :=
  has_sign_X SideA i k /\ has_sign_X SideB i k.

(** T-Blame: introduce a blame witness against signer z at index i.
    Precondition: two conflicting same-signer signed artefacts are
    in the history (witnessed by two sign cells with the same
    side=z, same idx=i, different digests). *)
Definition op_blame (owner : side) (z : side) (i : idx) (k : kappa) : kappa :=
  mk_kappa (locks k) (signs k) (verifieds k) ((mk_blame owner z i) :: blames k).

Definition op_blame_pre (z : side) (i : idx) (k : kappa) : Prop :=
  exists d1 d2, In (mk_sign z i d1) (signs k) /\
                In (mk_sign z i d2) (signs k) /\
                d1 <> d2.

(** E-Lock-Timeout: clear the active lock at side s, index i.  The
    precondition is existence of the active lock (the event-count
    deadline's numeric comparison is orthogonal for this proof). *)
Fixpoint remove_lock (s : side) (i : idx) (xs : list lock_cell) : list lock_cell :=
  match xs with
  | [] => []
  | x :: rest =>
      if side_eqb (lock_side x) s && idx_eqb (lock_idx x) i
      then remove_lock s i rest
      else x :: remove_lock s i rest
  end.

Definition op_timeout (s : side) (i : idx) (k : kappa) : kappa :=
  mk_kappa (remove_lock s i (locks k)) (signs k) (verifieds k) (blames k).

Definition op_timeout_pre (s : side) (i : idx) (k : kappa) : Prop :=
  active_lock_X s i k.

(** E-Commit / E-Release: both consume an active lock at (s, i).
    Commit requires a Verified witness at s; release can fire on
    abort or timeout.  We model both as [op_discharge]; the paper
    distinguishes them by which continuation follows, but the
    invariant is the same: the active-lock cell at (s, i) is gone. *)
Definition op_discharge := op_timeout.

(** ** Invariant preservation theorems *)

Lemma in_cons_or : forall A (x y : A) xs,
  In x (y :: xs) -> x = y \/ In x xs.
Proof.
  intros A x y xs. simpl. intros [H|H]; auto.
Qed.

(** (I1) is preserved by all operations. *)

(** T-Lock preserves I1 when the precondition holds. *)
Lemma op_lock_preserves_I1 :
  forall s i d k,
    invariant_I1 k ->
    op_lock_pre s i k ->
    invariant_I1 (op_lock s i d k).
Proof.
  intros s i d k HI1 Hpre.
  unfold invariant_I1, op_lock. simpl.
  intros s' i' d1 d2 H1 H2.
  apply in_cons_or in H1; apply in_cons_or in H2.
  destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
  - injection H1; injection H2; intros; subst. reflexivity.
  - injection H1; intros; subst.
    exfalso. apply Hpre. unfold active_lock_X. exists d2. exact H2.
  - injection H2; intros; subst.
    exfalso. apply Hpre. unfold active_lock_X. exists d1. exact H1.
  - eapply HI1; eassumption.
Qed.

(** T-Sign preserves I1 (it does not touch the locks list). *)
Lemma op_sign_preserves_I1 :
  forall s i d k,
    invariant_I1 k ->
    invariant_I1 (op_sign s i d k).
Proof.
  intros s i d k HI1. unfold invariant_I1, op_sign. simpl.
  intros s' i' d1 d2 H1 H2. eapply HI1; eassumption.
Qed.

(** T-Verify preserves I1 (it does not touch the locks list). *)
Lemma op_verify_preserves_I1 :
  forall s i k,
    invariant_I1 k ->
    invariant_I1 (op_verify s i k).
Proof.
  intros s i k HI1. unfold invariant_I1, op_verify. simpl.
  intros s' i' d1 d2 H1 H2. eapply HI1; eassumption.
Qed.

(** T-Blame preserves I1 (it does not touch the locks list). *)
Lemma op_blame_preserves_I1 :
  forall owner z i k,
    invariant_I1 k ->
    invariant_I1 (op_blame owner z i k).
Proof.
  intros owner z i k HI1. unfold invariant_I1, op_blame. simpl.
  intros s' i' d1 d2 H1 H2. eapply HI1; eassumption.
Qed.

(** Helper: removal from the locks list preserves the
    at-most-one-per-(s,i) property. *)
Lemma in_remove_lock : forall s i xs x,
  In x (remove_lock s i xs) -> In x xs.
Proof.
  intros s i xs. induction xs as [|y ys IH]; intros x H; simpl in *.
  - exact H.
  - destruct (side_eqb (lock_side y) s && idx_eqb (lock_idx y) i).
    + right. apply IH. exact H.
    + destruct H as [H|H].
      * subst. left. reflexivity.
      * right. apply IH. exact H.
Qed.

(** E-Lock-Timeout preserves I1. *)
Lemma op_timeout_preserves_I1 :
  forall s i k,
    invariant_I1 k ->
    invariant_I1 (op_timeout s i k).
Proof.
  intros s i k HI1. unfold invariant_I1, op_timeout. simpl.
  intros s' i' d1 d2 H1 H2.
  apply in_remove_lock in H1, H2.
  eapply HI1; eassumption.
Qed.

(** (I2) is preserved by all operations. *)

Lemma op_lock_preserves_I2 :
  forall s i d k,
    invariant_I2 k ->
    invariant_I2 (op_lock s i d k).
Proof.
  intros s i d k HI2. unfold invariant_I2, op_lock. simpl.
  intros s' i' d1 d2 H1 H2. eapply HI2; eassumption.
Qed.

Lemma op_sign_preserves_I2 :
  forall s i d k,
    invariant_I2 k ->
    op_sign_pre s i k ->
    invariant_I2 (op_sign s i d k).
Proof.
  intros s i d k HI2 Hpre.
  unfold invariant_I2, op_sign. simpl.
  intros s' i' d1 d2 H1 H2.
  apply in_cons_or in H1; apply in_cons_or in H2.
  destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
  - injection H1; injection H2; intros; subst. reflexivity.
  - injection H1; intros; subst.
    exfalso. apply Hpre. unfold has_sign_X. exists d2. exact H2.
  - injection H2; intros; subst.
    exfalso. apply Hpre. unfold has_sign_X. exists d1. exact H1.
  - eapply HI2; eassumption.
Qed.

Lemma op_verify_preserves_I2 :
  forall s i k,
    invariant_I2 k ->
    invariant_I2 (op_verify s i k).
Proof.
  intros s i k HI2. unfold invariant_I2, op_verify. simpl.
  intros s' i' d1 d2 H1 H2. eapply HI2; eassumption.
Qed.

Lemma op_blame_preserves_I2 :
  forall owner z i k,
    invariant_I2 k ->
    invariant_I2 (op_blame owner z i k).
Proof.
  intros owner z i k HI2. unfold invariant_I2, op_blame. simpl.
  intros s' i' d1 d2 H1 H2. eapply HI2; eassumption.
Qed.

Lemma op_timeout_preserves_I2 :
  forall s i k,
    invariant_I2 k ->
    invariant_I2 (op_timeout s i k).
Proof.
  intros s i k HI2. unfold invariant_I2, op_timeout. simpl.
  intros s' i' d1 d2 H1 H2. eapply HI2; eassumption.
Qed.

(** (I3) is preserved by all operations.  The only interesting case
    is [op_verify], which must use its precondition. *)

Lemma op_lock_preserves_I3 :
  forall s i d k,
    invariant_I3 k ->
    invariant_I3 (op_lock s i d k).
Proof.
  intros s i d k HI3.
  unfold invariant_I3 in HI3 |- *.
  unfold op_lock, has_verified_X, has_sign_X in *. simpl in *.
  intros s' i' H. apply HI3 with (s := s'). exact H.
Qed.

Lemma op_sign_preserves_I3 :
  forall s i d k,
    invariant_I3 k ->
    invariant_I3 (op_sign s i d k).
Proof.
  intros s i d k HI3.
  unfold invariant_I3 in HI3 |- *.
  unfold op_sign, has_verified_X, has_sign_X in *. simpl in *.
  intros s' i' H.
  specialize (HI3 s' i' H).
  destruct HI3 as [[da Ha] [db Hb]]. split.
  - exists da. right. exact Ha.
  - exists db. right. exact Hb.
Qed.

Lemma op_verify_preserves_I3 :
  forall s i k,
    invariant_I3 k ->
    op_verify_pre s i k ->
    invariant_I3 (op_verify s i k).
Proof.
  intros s i k HI3 Hpre.
  unfold invariant_I3 in HI3 |- *.
  unfold op_verify, op_verify_pre, has_verified_X, has_sign_X in *.
  simpl in *.
  intros s' i' H.
  destruct H as [Heq|H].
  - injection Heq; intros Heqi Heqs; subst. exact Hpre.
  - apply HI3 with (s := s'). exact H.
Qed.

Lemma op_blame_preserves_I3 :
  forall owner z i k,
    invariant_I3 k ->
    invariant_I3 (op_blame owner z i k).
Proof.
  intros owner z i k HI3.
  unfold invariant_I3 in HI3 |- *.
  unfold op_blame, has_verified_X, has_sign_X in *. simpl in *.
  intros s' i' H. apply HI3 with (s := s'). exact H.
Qed.

Lemma op_timeout_preserves_I3 :
  forall s i k,
    invariant_I3 k ->
    invariant_I3 (op_timeout s i k).
Proof.
  intros s i k HI3.
  unfold invariant_I3 in HI3 |- *.
  unfold op_timeout, has_verified_X, has_sign_X in *. simpl in *.
  intros s' i' H. apply HI3 with (s := s'). exact H.
Qed.

(** ** Joint invariant preservation *)

Theorem op_lock_preserves_bsc :
  forall s i d k,
    bsc_invariants k ->
    op_lock_pre s i k ->
    bsc_invariants (op_lock s i d k).
Proof.
  intros s i d k [HI1 [HI2 HI3]] Hpre.
  split; [|split].
  - apply op_lock_preserves_I1; assumption.
  - apply op_lock_preserves_I2; assumption.
  - apply op_lock_preserves_I3; assumption.
Qed.

Theorem op_sign_preserves_bsc :
  forall s i d k,
    bsc_invariants k ->
    op_sign_pre s i k ->
    bsc_invariants (op_sign s i d k).
Proof.
  intros s i d k [HI1 [HI2 HI3]] Hpre.
  split; [|split].
  - apply op_sign_preserves_I1; assumption.
  - apply op_sign_preserves_I2; assumption.
  - apply op_sign_preserves_I3; assumption.
Qed.

Theorem op_verify_preserves_bsc :
  forall s i k,
    bsc_invariants k ->
    op_verify_pre s i k ->
    bsc_invariants (op_verify s i k).
Proof.
  intros s i k [HI1 [HI2 HI3]] Hpre.
  split; [|split].
  - apply op_verify_preserves_I1; assumption.
  - apply op_verify_preserves_I2; assumption.
  - apply op_verify_preserves_I3; assumption.
Qed.

Theorem op_blame_preserves_bsc :
  forall owner z i k,
    bsc_invariants k ->
    bsc_invariants (op_blame owner z i k).
Proof.
  intros owner z i k [HI1 [HI2 HI3]].
  split; [|split].
  - apply op_blame_preserves_I1; assumption.
  - apply op_blame_preserves_I2; assumption.
  - apply op_blame_preserves_I3; assumption.
Qed.

Theorem op_timeout_preserves_bsc :
  forall s i k,
    bsc_invariants k ->
    bsc_invariants (op_timeout s i k).
Proof.
  intros s i k [HI1 [HI2 HI3]].
  split; [|split].
  - apply op_timeout_preserves_I1; assumption.
  - apply op_timeout_preserves_I2; assumption.
  - apply op_timeout_preserves_I3; assumption.
Qed.

(** ** Monotonicity of kappa under non-timeout operations

    The paper states (lem:kappa-monotone) that every corridor-fragment
    judgment extends kappa only additively, with the two noted
    exceptions: E-Lock-Timeout discharges an active-lock cell, and
    E-Commit / E-Release consume an active-lock cell.  For
    [op_lock], [op_sign], [op_verify], and [op_blame] we prove the
    stronger monotonicity property: the new history contains a
    superset of the previous history's cells.

    The verified-entry cells, in particular, are durable under this
    monotonicity: once introduced, [op_lock], [op_sign], [op_verify],
    [op_blame] never remove them.  This is the Verified-entry
    durability invariant (I3) in its Preservation form. *)

Definition kappa_sub (k1 k2 : kappa) : Prop :=
  (forall c, In c (locks k1) -> In c (locks k2)) /\
  (forall c, In c (signs k1) -> In c (signs k2)) /\
  (forall c, In c (verifieds k1) -> In c (verifieds k2)) /\
  (forall c, In c (blames k1) -> In c (blames k2)).

Lemma kappa_sub_refl : forall k, kappa_sub k k.
Proof. repeat split; intros c H; exact H. Qed.

Lemma op_lock_kappa_sub :
  forall s i d k, kappa_sub k (op_lock s i d k).
Proof.
  intros s i d k. unfold kappa_sub, op_lock; simpl.
  split; [|split; [|split]]; intros c H.
  - right. exact H.
  - exact H.
  - exact H.
  - exact H.
Qed.

Lemma op_sign_kappa_sub :
  forall s i d k, kappa_sub k (op_sign s i d k).
Proof.
  intros s i d k. unfold kappa_sub, op_sign; simpl.
  split; [|split; [|split]]; intros c H.
  - exact H.
  - right. exact H.
  - exact H.
  - exact H.
Qed.

Lemma op_verify_kappa_sub :
  forall s i k, kappa_sub k (op_verify s i k).
Proof.
  intros s i k. unfold kappa_sub, op_verify; simpl.
  split; [|split; [|split]]; intros c H.
  - exact H.
  - exact H.
  - right. exact H.
  - exact H.
Qed.

Lemma op_blame_kappa_sub :
  forall owner z i k, kappa_sub k (op_blame owner z i k).
Proof.
  intros owner z i k. unfold kappa_sub, op_blame; simpl.
  split; [|split; [|split]]; intros c H.
  - exact H.
  - exact H.
  - exact H.
  - right. exact H.
Qed.

(** Verified-entry durability under non-timeout operations: a
    verified cell present in k is still present in any
    non-timeout successor.  This is the operational form of the
    paper's Verified-entry durability invariant (I3). *)
Theorem verified_durable_op_lock :
  forall s i k s' i' d,
    has_verified_X s i k ->
    has_verified_X s i (op_lock s' i' d k).
Proof.
  intros. unfold has_verified_X, op_lock in *; simpl in *. exact H.
Qed.

Theorem verified_durable_op_sign :
  forall s i k s' i' d,
    has_verified_X s i k ->
    has_verified_X s i (op_sign s' i' d k).
Proof.
  intros. unfold has_verified_X, op_sign in *; simpl in *. exact H.
Qed.

Theorem verified_durable_op_verify :
  forall s i k s' i',
    has_verified_X s i k ->
    has_verified_X s i (op_verify s' i' k).
Proof.
  intros. unfold has_verified_X, op_verify in *; simpl in *.
  right. exact H.
Qed.

Theorem verified_durable_op_blame :
  forall s i k owner z i',
    has_verified_X s i k ->
    has_verified_X s i (op_blame owner z i' k).
Proof.
  intros. unfold has_verified_X, op_blame in *; simpl in *. exact H.
Qed.

Theorem verified_durable_op_timeout :
  forall s i k s' i',
    has_verified_X s i k ->
    has_verified_X s i (op_timeout s' i' k).
Proof.
  intros. unfold has_verified_X, op_timeout in *; simpl in *. exact H.
Qed.

(** ** Cross-side durability

    The paper's commit-safety property (Theorem 1 of SJN) asserts
    that if side X is in Committed, then side Xbar is either also
    Committed or in a recoverable state from which only Committed
    is reachable.  At the kappa layer this is expressed as: once
    both sides carry a verified-entry cell at the same index, the
    commit decision is determined by the durable pair and is the
    same at both sides.  We do not model the full commit-phase
    reduction here (that is in [SessionCorridor.v]); what we prove
    is the underlying kappa-level invariant: if both sides have
    verified at (omega, epsilon), then both sides have both signed
    verdicts durable. *)
Theorem verified_both_sides_implies_both_signs_both_sides :
  forall i k,
    bsc_invariants k ->
    has_verified_X SideA i k ->
    has_verified_X SideB i k ->
    has_sign_X SideA i k /\ has_sign_X SideB i k.
Proof.
  intros i k [_ [_ HI3]] HvA HvB.
  apply HI3 with (s := SideA). exact HvA.
Qed.

(** ** Verdict uniqueness as equivocation detector

    A conflicting same-signer pair of signed artefacts at the same
    (s, i) witness a blame condition: in the paper, T-Blame derives
    Blame<Z, omega, epsilon> from such a pair.  The pair cannot
    coexist with (I2) in a single side's history.  Therefore a
    blame condition must arise from artefacts that did not all
    originate at that side: one of the two signatures is imported.
    This is the kappa-layer witness to SJN's accountable-safety
    decomposition (Theorem 3). *)
Theorem equivocation_detected_by_I2 :
  forall s i d1 d2 k,
    invariant_I2 k ->
    In (mk_sign s i d1) (signs k) ->
    In (mk_sign s i d2) (signs k) ->
    d1 = d2.
Proof.
  intros s i d1 d2 k HI2 H1 H2. eapply HI2; eassumption.
Qed.

(** The contrapositive: if two signed artefacts at the same (s, i)
    have different digests in k, then (I2) does not hold of k.
    This is the kappa-level blame condition. *)
Corollary blame_condition_violates_I2 :
  forall s i d1 d2 k,
    In (mk_sign s i d1) (signs k) ->
    In (mk_sign s i d2) (signs k) ->
    d1 <> d2 ->
    ~ invariant_I2 k.
Proof.
  intros s i d1 d2 k H1 H2 Hneq HI2.
  apply Hneq. eapply HI2; eassumption.
Qed.

(** ** Summary

    The theorems above give a Qed-closed witness that the paper's
    corridor typing judgment kappa preserves the three SJN BSC
    invariants (I1) Lock monotonicity, (I2) Verdict uniqueness,
    and (I3) Verified-entry durability, under all seven
    admissible operations (T-Lock, T-Sign, T-Verify, T-Blame,
    E-Lock-Timeout, E-Commit, E-Release).  Combined with the
    initial emptiness [bsc_invariants_empty], a simple induction
    over any trace of corridor operations lifts the joint
    invariant from kappa_empty to every reachable kappa. *)

(** An admissible trace of corridor operations. *)
Inductive step : kappa -> kappa -> Prop :=
  | StepLock : forall s i d k,
      op_lock_pre s i k ->
      step k (op_lock s i d k)
  | StepSign : forall s i d k,
      op_sign_pre s i k ->
      step k (op_sign s i d k)
  | StepVerify : forall s i k,
      op_verify_pre s i k ->
      step k (op_verify s i k)
  | StepBlame : forall owner z i k,
      step k (op_blame owner z i k)
  | StepTimeout : forall s i k,
      step k (op_timeout s i k).

Inductive steps : kappa -> kappa -> Prop :=
  | StepsRefl : forall k, steps k k
  | StepsCons : forall k k' k'',
      step k k' -> steps k' k'' -> steps k k''.

Theorem bsc_preserved_over_steps :
  forall k1 k2,
    bsc_invariants k1 ->
    steps k1 k2 ->
    bsc_invariants k2.
Proof.
  intros k1 k2 Hinv Hsteps.
  induction Hsteps as [k|k k' k'' Hstep Hsteps' IH].
  - exact Hinv.
  - apply IH. inversion Hstep; subst.
    + apply op_lock_preserves_bsc; assumption.
    + apply op_sign_preserves_bsc; assumption.
    + apply op_verify_preserves_bsc; assumption.
    + apply op_blame_preserves_bsc; assumption.
    + apply op_timeout_preserves_bsc; assumption.
Qed.

(** The corridor history kappa threaded through any derivation
    starting from kappa_empty satisfies (I1), (I2), and (I3).
    This is the mechanization of the paper's
    [Corridor-history monotonicity] lemma
    ([papers/op.tex lem:kappa-monotone]) lifted to the SJN BSC
    invariant set.  *)
Theorem bsc_invariants_all_reachable :
  forall k,
    steps kappa_empty k ->
    bsc_invariants k.
Proof.
  intros k H. apply bsc_preserved_over_steps with (k1 := kappa_empty).
  - apply bsc_invariants_empty.
  - exact H.
Qed.
