Require Import Relations.

Set Implicit Arguments.


Section Invariant.
  Variable state : Type.
  Variable step : state -> state -> Prop.
  Variable invariant : state -> Prop.

  Hint Constructors trc.

  Definition safe (s : state) :=
    forall s', step^* s s' -> invariant s'.

  Variable s0 : state.

  Hypothesis Hinitial : invariant s0.

  Hypothesis Hstep : forall s s', invariant s -> step s s' -> invariant s'.

  Lemma safety : safe s0.
  Proof.
    generalize dependent s0.
    unfold safe.
    induction 2; eauto.
  Qed.
End Invariant.

Hint Resolve safety.
