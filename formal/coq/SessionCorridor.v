From Stdlib Require Import List.
Import ListNotations.

(** * SessionCorridor.v

    A compact mechanization of the fixed corridor session from
    [papers/op.tex].  The file proves the two paper-level session
    theorems directly on the protocol state machine:

    - deadlock freedom of the endpoint projections, and
    - session safety through the terminal Commit / Abort states. *)

Set Implicit Arguments.

Inductive Decision : Type :=
  | Commit
  | Abort.

Inductive Message : Type :=
  | MsgTensorRequest
  | MsgLockedTensor
  | MsgVerdictI
  | MsgVerdictR
  | MsgDecision : Decision -> Message.

Inductive EndpointAction : Type :=
  | ActSend : Message -> EndpointAction
  | ActRecv : Message -> EndpointAction
  | ActEnd : EndpointAction.

Inductive InitiatorState : Type :=
  | I0_Request
  | I1_Locked
  | I2_VerdictI
  | I3_VerdictR
  | I4_Decision
  | IEnd : Decision -> InitiatorState.

Inductive ResponderState : Type :=
  | R0_Request
  | R1_Locked
  | R2_VerdictI
  | R3_VerdictR
  | R4_Decision
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
  | IEnd _ => ActEnd
  end.

Definition responder_action (d : Decision) (st : ResponderState) : EndpointAction :=
  match st with
  | R0_Request => ActRecv MsgTensorRequest
  | R1_Locked => ActSend MsgLockedTensor
  | R2_VerdictI => ActRecv MsgVerdictI
  | R3_VerdictR => ActSend MsgVerdictR
  | R4_Decision => ActRecv (MsgDecision d)
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
  | Reach5 : reachable_pair d (IEnd d, REnd d).

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
      corridor_step d (I4_Decision, R4_Decision) (IEnd d, REnd d).

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
  eapply StepsCons.
  - apply StepTensorRequest.
  - eapply StepsCons.
    + apply StepLockedTensor.
    + eapply StepsCons.
      * apply StepVerdictI.
      * eapply StepsCons.
        -- apply StepVerdictR.
        -- eapply StepsCons.
           ++ apply StepDecision.
           ++ apply StepsRefl.
Qed.

Theorem no_mixed_decision :
  forall (d1 d2 : Decision),
    reachable_pair d1 (IEnd d1, REnd d2) ->
    d1 = d2.
Proof.
  intros d1 d2 Hreach.
  inversion Hreach; reflexivity.
Qed.

Theorem session_safety :
  forall (d : Decision),
    corridor_steps d initial_pair (terminal_pair d) /\
    reachable_pair d (terminal_pair d) /\
    dual_action (initiator_action d (fst (terminal_pair d)))
                (responder_action d (snd (terminal_pair d))) /\
    (forall d', reachable_pair d (IEnd d, REnd d') -> d = d').
Proof.
  intro d.
  repeat split.
  - apply corridor_reaches_terminal.
  - apply Reach5.
  - simpl. constructor.
  - intros d' Hreach.
    apply no_mixed_decision.
    exact Hreach.
Qed.
