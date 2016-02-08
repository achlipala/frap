Require Import Relations.


Definition invariantFor {state} (initial : state -> Prop) (step : state -> state -> Prop) (invariant : state -> Prop) :=
  forall s, initial s
            -> forall s', step^* s s'
                          -> invariant s'.

Theorem use_invariant : forall {state} (initial : state -> Prop)
  (step : state -> state -> Prop) (invariant : state -> Prop) s s',
  step^* s s'
  -> initial s
  -> invariantFor initial step invariant
  -> invariant s'.
Proof.
  firstorder.
Qed.

Theorem invariantFor_monotone : forall {state} (initial : state -> Prop)
  (step : state -> state -> Prop) (invariant1 invariant2 : state -> Prop),
  (forall s, invariant1 s -> invariant2 s)
  -> invariantFor initial step invariant1
  -> invariantFor initial step invariant2.
Proof.
  unfold invariantFor; intuition eauto.
Qed.

Theorem invariant_induction : forall {state} (initial : state -> Prop)
  (step : state -> state -> Prop) (invariant : state -> Prop),
  (forall s, initial s -> invariant s)
  -> (forall s, invariant s -> forall s', step s s' -> invariant s')
  -> invariantFor initial step invariant.
Proof.
  unfold invariantFor; intros.
  assert (invariant s) by eauto.
  clear H1.
  induction H2; eauto.
Qed.
