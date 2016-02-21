Require Import Invariant Sets.

Definition oneStepClosure_current {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  forall st, invariant1 st
             -> invariant2 st.

Definition oneStepClosure_new {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  forall st st', invariant1 st
                 -> sys.(Step) st st'
                 -> invariant2 st'.

Definition oneStepClosure {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  oneStepClosure_current sys invariant1 invariant2
  /\ oneStepClosure_new sys invariant1 invariant2.

Theorem prove_oneStepClosure : forall state (sys : trsys state) (inv1 inv2 : state -> Prop),
  (forall st, inv1 st -> inv2 st)
  -> (forall st st', inv1 st -> sys.(Step) st st' -> inv2 st')
  -> oneStepClosure sys inv1 inv2.
Proof.
  unfold oneStepClosure; tauto.
Qed.

Theorem oneStepClosure_done : forall state (sys : trsys state) (invariant : state -> Prop),
  (forall st, sys.(Initial) st -> invariant st)
  -> oneStepClosure sys invariant invariant
  -> invariantFor sys invariant.
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new.
  intuition eauto using invariant_induction.
Qed.

Inductive multiStepClosure {state} (sys : trsys state)
  : (state -> Prop) -> (state -> Prop) -> Prop :=
| MscDone : forall inv,
    oneStepClosure sys inv inv
    -> multiStepClosure sys inv inv
| MscStep : forall inv inv' inv'',
    oneStepClosure sys inv inv'
    -> multiStepClosure sys inv' inv''
    -> multiStepClosure sys inv inv''.

Lemma multiStepClosure_ok' : forall state (sys : trsys state) (inv inv' : state -> Prop),
  multiStepClosure sys inv inv'
  -> (forall st, sys.(Initial) st -> inv st)
  -> invariantFor sys inv'.
Proof.
  induction 1; simpl; intuition eauto using oneStepClosure_done.

  unfold oneStepClosure, oneStepClosure_current in *.
  intuition eauto.
Qed.

Theorem multiStepClosure_ok : forall state (sys : trsys state) (inv : state -> Prop),
  multiStepClosure sys sys.(Initial) inv
  -> invariantFor sys inv.
Proof.
  eauto using multiStepClosure_ok'.
Qed.

Theorem oneStepClosure_empty : forall state (sys : trsys state),
  oneStepClosure sys (constant nil) (constant nil).
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new; intuition.
Qed.

Theorem oneStepClosure_split : forall state (sys : trsys state) st sts (inv1 inv2 : state -> Prop),
  (forall st', sys.(Step) st st' -> inv1 st')
  -> oneStepClosure sys (constant sts) inv2
  -> oneStepClosure sys (constant (st :: sts)) ({st} \cup inv1 \cup inv2).
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new; intuition.

  inversion H0; subst.
  unfold union; simpl; tauto.

  unfold union; simpl; eauto.

  unfold union in *; simpl in *.
  intuition (subst; eauto).
Qed.

Theorem singleton_in : forall {A} (x : A) rest,
  ({x} \cup rest) x.
Proof.
  unfold union; simpl; auto.
Qed.

Theorem singleton_in_other : forall {A} (x : A) (s1 s2 : set A),
  s2 x
  -> (s1 \cup s2) x.
Proof.
  unfold union; simpl; auto.
Qed.
