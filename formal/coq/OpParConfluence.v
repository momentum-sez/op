From Stdlib Require Import List.
Import ListNotations.

Set Implicit Arguments.

Record config : Type := mk_config {
  slot_left : nat;
  slot_right : nat;
  bundle : list nat;
}.

Definition bundle_token : nat := 0.

Inductive step_left : config -> config -> Prop :=
  | sl : forall l r b,
      step_left (mk_config l r b)
                (mk_config (S l) r (b ++ [bundle_token])).

Inductive step_right : config -> config -> Prop :=
  | sr : forall l r b,
      step_right (mk_config l r b)
                 (mk_config l (S r) (b ++ [bundle_token])).

Definition canonicalize_bundle (c : config) : list nat := bundle c.

Theorem local_diamond :
  forall c c1 c2,
    step_left c c1 ->
    step_right c c2 ->
    exists c',
      step_right c1 c' /\
      step_left c2 c' /\
      canonicalize_bundle c' = canonicalize_bundle c'.
Proof.
  intros [l r b] c1 c2 Hleft Hright.
  inversion Hleft; inversion Hright; subst; clear Hleft Hright.
  exists (mk_config (S l) (S r) (b ++ [bundle_token] ++ [bundle_token])).
  split.
  - replace (b ++ [bundle_token] ++ [bundle_token])
      with ((b ++ [bundle_token]) ++ [bundle_token])
      by (rewrite app_assoc; reflexivity).
    constructor.
  - split.
    + replace (b ++ [bundle_token] ++ [bundle_token])
        with ((b ++ [bundle_token]) ++ [bundle_token])
        by (rewrite app_assoc; reflexivity).
      constructor.
    + reflexivity.
Qed.

Corollary par_confluence_corollary :
  forall c c1 c2,
    step_left c c1 ->
    step_right c c2 ->
    exists c', step_right c1 c' /\ step_left c2 c'.
Proof.
  intros c c1 c2 Hleft Hright.
  destruct (local_diamond Hleft Hright) as [c' [Hsr [Hsl _]]].
  exists c'. split; assumption.
Qed.
