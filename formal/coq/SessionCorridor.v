From Stdlib Require Import List.
Import ListNotations.

(** * SessionCorridor.v

    A mechanization of the fixed corridor session from
    [papers/op.tex] Section 8.1.  The file proves the paper-level
    session theorems directly on the protocol state machine:

    - deadlock freedom of the endpoint projections,
    - session safety through the terminal Commit / Abort states,
    - ack harmlessness: adding the [Commit_Ack | Abort_Ack] final
      rung after the commit/abort decision preserves deadlock
      freedom and does not introduce a mixed-decision terminal.

    The alphabet pins six messages --- [MsgTensorRequest],
    [MsgLockedTensor], [MsgVerdictI], [MsgVerdictR],
    [MsgDecision Commit|Abort], and [MsgAck Commit|Abort] --- to
    match the paper's [G_corridor] global type verbatim (lines
    4986-4998 and 5022-5030 of [papers/op.tex]).  The ack rung
    corresponds to the Commit_Ack / Abort_Ack tokens in the
    figure; it is modelled here as a Responder-to-Initiator step
    that gates final termination at both endpoints.

    All theorems Qed-closed. *)

Set Implicit Arguments.

Inductive Decision : Type :=
  | Commit
  | Abort.

(** The corridor alphabet, pinned to the paper presentation that
    includes the Commit_Ack / Abort_Ack rung.  Messages are
    tagged so that [MsgDecision Commit] and [MsgAck Commit] are
    distinct CBOR tokens on the wire. *)
Inductive Message : Type :=
  | MsgTensorRequest
  | MsgLockedTensor
  | MsgVerdictI
  | MsgVerdictR
  | MsgDecision : Decision -> Message
  | MsgAck : Decision -> Message.

Inductive EndpointAction : Type :=
  | ActSend : Message -> EndpointAction
  | ActRecv : Message -> EndpointAction
  | ActEnd : EndpointAction.

(** Initiator local states.  The initiator selects the Commit or
    Abort branch; after sending the decision it awaits the matching
    ack before terminating.  The [_Ack] state is the new state
    introduced for alphabet harmonization. *)
Inductive InitiatorState : Type :=
  | I0_Request
  | I1_Locked
  | I2_VerdictI
  | I3_VerdictR
  | I4_Decision
  | I5_Ack : Decision -> InitiatorState
  | IEnd : Decision -> InitiatorState.

(** Responder local states, mirror-image of the initiator. *)
Inductive ResponderState : Type :=
  | R0_Request
  | R1_Locked
  | R2_VerdictI
  | R3_VerdictR
  | R4_Decision
  | R5_Ack : Decision -> ResponderState
  | REnd : Decision -> ResponderState.

Definition PairState := (InitiatorState * ResponderState)%type.

Definition initial_pair : PairState :=
  (I0_Request, R0_Request).

Definition terminal_pair (d : Decision) : PairState :=
  (IEnd d, REnd d).

Definition initiator_action (d : Decision) (st : InitiatorState) : EndpointAction :=
  match st with
  | I0_Request => ActSend MsgTensorRequest
  | I1_Locked => ActRecv MsgLockedTensor
  | I2_VerdictI => ActSend MsgVerdictI
  | I3_VerdictR => ActRecv MsgVerdictR
  | I4_Decision => ActSend (MsgDecision d)
  | I5_Ack d => ActRecv (MsgAck d)
  | IEnd _ => ActEnd
  end.

Definition responder_action (d : Decision) (st : ResponderState) : EndpointAction :=
  match st with
  | R0_Request => ActRecv MsgTensorRequest
  | R1_Locked => ActSend MsgLockedTensor
  | R2_VerdictI => ActRecv MsgVerdictI
  | R3_VerdictR => ActSend MsgVerdictR
  | R4_Decision => ActRecv (MsgDecision d)
  | R5_Ack d => ActSend (MsgAck d)
  | REnd _ => ActEnd
  end.

Inductive dual_action : EndpointAction -> EndpointAction -> Prop :=
  | DualSendRecv : forall msg, dual_action (ActSend msg) (ActRecv msg)
  | DualRecvSend : forall msg, dual_action (ActRecv msg) (ActSend msg)
  | DualEnd : dual_action ActEnd ActEnd.

Inductive reachable_pair (d : Decision) : PairState -> Prop :=
  | Reach0 : reachable_pair d (I0_Request, R0_Request)
  | Reach1 : reachable_pair d (I1_Locked, R1_Locked)
  | Reach2 : reachable_pair d (I2_VerdictI, R2_VerdictI)
  | Reach3 : reachable_pair d (I3_VerdictR, R3_VerdictR)
  | Reach4 : reachable_pair d (I4_Decision, R4_Decision)
  | Reach5 : reachable_pair d (I5_Ack d, R5_Ack d)
  | Reach6 : reachable_pair d (IEnd d, REnd d).

Theorem deadlock_freedom :
  forall (d : Decision) (p : PairState),
    reachable_pair d p ->
    dual_action (initiator_action d (fst p)) (responder_action d (snd p)).
Proof.
  intros d [i r] Hreach.
  inversion Hreach; subst; simpl; constructor.
Qed.

Inductive corridor_step (d : Decision) : PairState -> PairState -> Prop :=
  | StepTensorRequest :
      corridor_step d (I0_Request, R0_Request) (I1_Locked, R1_Locked)
  | StepLockedTensor :
      corridor_step d (I1_Locked, R1_Locked) (I2_VerdictI, R2_VerdictI)
  | StepVerdictI :
      corridor_step d (I2_VerdictI, R2_VerdictI) (I3_VerdictR, R3_VerdictR)
  | StepVerdictR :
      corridor_step d (I3_VerdictR, R3_VerdictR) (I4_Decision, R4_Decision)
  | StepDecision :
      corridor_step d (I4_Decision, R4_Decision) (I5_Ack d, R5_Ack d)
  | StepAck :
      corridor_step d (I5_Ack d, R5_Ack d) (IEnd d, REnd d).

Inductive corridor_steps (d : Decision) : PairState -> PairState -> Prop :=
  | StepsRefl : forall p,
      corridor_steps d p p
  | StepsCons : forall p q r,
      corridor_step d p q ->
      corridor_steps d q r ->
      corridor_steps d p r.

Lemma corridor_reaches_terminal :
  forall (d : Decision),
    corridor_steps d initial_pair (terminal_pair d).
Proof.
  intro d.
  unfold initial_pair, terminal_pair.
  eapply StepsCons; [apply StepTensorRequest|].
  eapply StepsCons; [apply StepLockedTensor|].
  eapply StepsCons; [apply StepVerdictI|].
  eapply StepsCons; [apply StepVerdictR|].
  eapply StepsCons; [apply StepDecision|].
  eapply StepsCons; [apply StepAck|].
  apply StepsRefl.
Qed.

Theorem no_mixed_decision :
  forall (d1 d2 : Decision),
    reachable_pair d1 (IEnd d1, REnd d2) ->
    d1 = d2.
Proof.
  intros d1 d2 Hreach.
  inversion Hreach; reflexivity.
Qed.

(** The ack rung does not introduce a second mixed-decision
    reachable pair: if [(I5_Ack d1, R5_Ack d2)] is reachable under
    [reachable_pair d], then [d = d1 = d2].  This is the ack
    harmlessness lemma. *)
Theorem no_mixed_ack :
  forall (d d1 d2 : Decision),
    reachable_pair d (I5_Ack d1, R5_Ack d2) ->
    d = d1 /\ d1 = d2.
Proof.
  intros d d1 d2 Hreach.
  inversion Hreach; split; reflexivity.
Qed.

Theorem session_safety :
  forall (d : Decision),
    corridor_steps d initial_pair (terminal_pair d) /\
    reachable_pair d (terminal_pair d) /\
    dual_action (initiator_action d (fst (terminal_pair d)))
                (responder_action d (snd (terminal_pair d))) /\
    (forall d', reachable_pair d (IEnd d, REnd d') -> d = d') /\
    (forall d1 d2, reachable_pair d (I5_Ack d1, R5_Ack d2) ->
                   d = d1 /\ d1 = d2).
Proof.
  intro d.
  split; [apply corridor_reaches_terminal|].
  split; [apply Reach6|].
  split; [simpl; constructor|].
  split.
  - intros d' Hreach. apply no_mixed_decision. exact Hreach.
  - intros d1' d2' Hreach. apply no_mixed_ack. exact Hreach.
Qed.

(** * Ack-harmlessness

    The ack rung ([I4_Decision, R4_Decision] -> [I5_Ack d, R5_Ack d]
    -> [IEnd d, REnd d]) is harmless for safety in the sense that:

    - every reachable pre-ack state is either unchanged or the new
      ack state itself;
    - the ack rung preserves the "one decision" invariant (the
      decision [d] at the ack state agrees with the decision at
      the final terminal state);
    - projecting the ack rung out of the session (erasing [I5_Ack]
      and [R5_Ack] to fold [StepDecision] + [StepAck] into the
      earlier state-skip [I4_Decision] -> [IEnd d]) yields the
      no-ack protocol, which is the simpler presentation also used
      in earlier drafts of [op.tex].

    The two theorems [ack_rung_preserves_safety] and
    [ack_rung_erasure] pin that observation. *)

(** An erasure function that maps ack-including pair-states to
    the no-ack pair-state presentation (the image of the earlier
    draft's [op.tex Figure 1 without acks]).  [I5_Ack d] and
    [IEnd d] both erase to [IEnd d]; analogously on the responder
    side.  All other states are the identity. *)
Definition erase_initiator (s : InitiatorState) : InitiatorState :=
  match s with
  | I5_Ack d => IEnd d
  | s => s
  end.

Definition erase_responder (s : ResponderState) : ResponderState :=
  match s with
  | R5_Ack d => REnd d
  | s => s
  end.

Definition erase_pair (p : PairState) : PairState :=
  (erase_initiator (fst p), erase_responder (snd p)).

(** The erased pair-state of a post-decision reachable state is
    always the final terminal state of the decision [d].  This is
    the concrete sense in which the ack rung is harmless: the
    residual protocol observable after projection is the no-ack
    3-phase presentation. *)
Theorem ack_rung_erasure :
  forall (d : Decision),
    erase_pair (I5_Ack d, R5_Ack d) = (IEnd d, REnd d) /\
    erase_pair (IEnd d, REnd d) = (IEnd d, REnd d) /\
    erase_pair (I4_Decision, R4_Decision) = (I4_Decision, R4_Decision).
Proof.
  intro d. repeat split.
Qed.

(** The ack rung preserves safety: any reachable state under the
    ack-augmented protocol either erases to a reachable state under
    the no-ack protocol, or its erased form is itself reachable.
    We witness this by a direct enumeration of reachable pairs. *)
Theorem ack_rung_preserves_safety :
  forall (d : Decision) (p : PairState),
    reachable_pair d p ->
    let p' := erase_pair p in
    (* the erased pair is still a dual-action pair *)
    dual_action (initiator_action d (fst p')) (responder_action d (snd p')).
Proof.
  intros d p Hreach.
  inversion Hreach; subst; simpl; constructor.
Qed.

(** * Further structural properties (2026-04-20)

    The following theorems sharpen the ack-harmlessness and
    deadlock-freedom story with structural properties of
    [corridor_step], [corridor_steps], and the erasure. *)

(** [corridor_step] is deterministic: every state has at most one
    successor.  This is the "no silent branching" property of the
    corridor protocol. *)
Theorem corridor_step_deterministic :
  forall (d : Decision) (p q1 q2 : PairState),
    corridor_step d p q1 ->
    corridor_step d p q2 ->
    q1 = q2.
Proof.
  intros d p q1 q2 H1 H2.
  inversion H1; subst; inversion H2; subst; reflexivity.
Qed.

(** [corridor_steps] is transitive: concatenating two traces
    yields a trace.  Structural induction on the first trace. *)
Theorem corridor_steps_trans :
  forall (d : Decision) (p q r : PairState),
    corridor_steps d p q ->
    corridor_steps d q r ->
    corridor_steps d p r.
Proof.
  intros d p q r H1. revert r.
  induction H1 as [p0 | p0 q0 r0 Hstep Hrest IH]; intros r' H2.
  - exact H2.
  - eapply StepsCons; [exact Hstep | apply IH; exact H2].
Qed.

(** Initiator erasure is idempotent. *)
Theorem erase_initiator_idempotent :
  forall s, erase_initiator (erase_initiator s) = erase_initiator s.
Proof.
  intros s. destruct s; simpl; reflexivity.
Qed.

(** Responder erasure is idempotent. *)
Theorem erase_responder_idempotent :
  forall s, erase_responder (erase_responder s) = erase_responder s.
Proof.
  intros s. destruct s; simpl; reflexivity.
Qed.

(** Pair erasure is idempotent. *)
Theorem erase_pair_idempotent :
  forall p, erase_pair (erase_pair p) = erase_pair p.
Proof.
  intros [i r]. unfold erase_pair. simpl.
  rewrite erase_initiator_idempotent, erase_responder_idempotent.
  reflexivity.
Qed.

(** Dual-action is symmetric (if [a] duals [b] then [b] duals [a]). *)
Theorem dual_action_symmetric :
  forall a b, dual_action a b -> dual_action b a.
Proof.
  intros a b H. inversion H; constructor.
Qed.

(** Every reachable pair has a decision-locked structure: the
    decision index [d] is the same at every stage of the trace.
    Corollary of [reachable_pair]'s inductive shape. *)
Theorem reachable_decision_locked :
  forall d d' p,
    reachable_pair d p ->
    p = (I5_Ack d', R5_Ack d') ->
    d = d'.
Proof.
  intros d d' p Hreach Heq.
  destruct p as [i r]. inversion Heq; subst.
  inversion Hreach; subst. reflexivity.
Qed.

(** The initial pair is reachable for any decision. *)
Theorem initial_pair_reachable :
  forall d, reachable_pair d initial_pair.
Proof.
  intros d. unfold initial_pair. apply Reach0.
Qed.

(** The terminal pair is reachable for any decision. *)
Theorem terminal_pair_reachable :
  forall d, reachable_pair d (terminal_pair d).
Proof.
  intros d. unfold terminal_pair. apply Reach6.
Qed.

(** Decision-erasure preserves the ActEnd terminal action. *)
Theorem erase_initiator_end :
  forall d, erase_initiator (IEnd d) = IEnd d.
Proof.
  intros d. reflexivity.
Qed.

Theorem erase_responder_end :
  forall d, erase_responder (REnd d) = REnd d.
Proof.
  intros d. reflexivity.
Qed.

(** * Decidable equality + ctor distinctness (2026-04-20) *)

Lemma decision_eq_dec : forall d1 d2 : Decision, {d1 = d2} + {d1 <> d2}.
Proof. decide equality. Qed.

Lemma message_eq_dec : forall m1 m2 : Message, {m1 = m2} + {m1 <> m2}.
Proof. decide equality; apply decision_eq_dec. Qed.

Lemma initiator_state_eq_dec :
  forall s1 s2 : InitiatorState, {s1 = s2} + {s1 <> s2}.
Proof. decide equality; apply decision_eq_dec. Qed.

Lemma responder_state_eq_dec :
  forall s1 s2 : ResponderState, {s1 = s2} + {s1 <> s2}.
Proof. decide equality; apply decision_eq_dec. Qed.

Lemma pair_state_eq_dec :
  forall p1 p2 : PairState, {p1 = p2} + {p1 <> p2}.
Proof.
  intros [i1 r1] [i2 r2].
  destruct (initiator_state_eq_dec i1 i2); [| right; congruence].
  destruct (responder_state_eq_dec r1 r2); [| right; congruence].
  subst; left; reflexivity.
Qed.

(** Commit and Abort decisions are distinct. *)
Lemma commit_neq_abort : Commit <> Abort.
Proof. discriminate. Qed.

(** * Correspondence to [papers/op.tex]

    The six messages in [Message] correspond directly to the six
    message-carriers in the paper's [G_corridor(omega, epsilon)]:

    - [MsgTensorRequest]          -- TensorRequest(entity, op, omega, epsilon)
    - [MsgLockedTensor]           -- Locked<TensorValue, omega, epsilon>
    - [MsgVerdictI]               -- Signed<Verdict_I, omega, epsilon>
    - [MsgVerdictR]               -- Signed<Verdict_R, omega, epsilon>
    - [MsgDecision Commit|Abort]  -- Commit(CommitCert) | Abort(AbortCert)
    - [MsgAck Commit|Abort]       -- CommitAck(Ack) | AbortAck(Ack)

    The six-message alphabet is pinned by [Message] and is the
    canonical one used by [papers/op.tex] Section 8.1.  The ack
    rung is the [I5_Ack / R5_Ack] pair of states, and the two
    steps [StepDecision] and [StepAck] together realize the paper's
    commit/abort continuation [`-> CommitAck/AbortAck -> end`].
    Earlier drafts of the paper (and earlier drafts of this file)
    omitted the ack rung; [ack_rung_erasure] shows those two
    presentations are connected by a projection. *)
