(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 5: Model Checking
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap TransitionSystems.

Set Implicit Arguments.


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
  unfold oneStepClosure.
  propositional.
Qed.

Theorem oneStepClosure_done : forall state (sys : trsys state) (invariant : state -> Prop),
  (forall st, sys.(Initial) st -> invariant st)
  -> oneStepClosure sys invariant invariant
  -> invariantFor sys invariant.
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new.
  propositional.
  apply invariant_induction.
  assumption.
  simplify.
  eapply H2.
  eassumption.
  assumption.
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
  induct 1; simplify.

  apply oneStepClosure_done.
  assumption.
  assumption.

  apply IHmultiStepClosure.
  simplify.
  unfold oneStepClosure, oneStepClosure_current in *. (* <-- *)
  propositional.
  apply H3.
  apply H1.
  assumption.
Qed.

Theorem multiStepClosure_ok : forall state (sys : trsys state) (inv : state -> Prop),
  multiStepClosure sys sys.(Initial) inv
  -> invariantFor sys inv.
Proof.
  simplify.
  eapply multiStepClosure_ok'.
  eassumption.
  propositional.
Qed.

Theorem oneStepClosure_empty : forall state (sys : trsys state),
  oneStepClosure sys (constant nil) (constant nil).
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new; propositional.
Qed.

Theorem oneStepClosure_split : forall state (sys : trsys state) st sts (inv1 inv2 : state -> Prop),
  (forall st', sys.(Step) st st' -> inv1 st')
  -> oneStepClosure sys (constant sts) inv2
  -> oneStepClosure sys (constant (st :: sts)) ({st} \cup inv1 \cup inv2).
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new; propositional.

  invert H0.

  left.
  left.
  simplify.
  propositional.

  right.
  apply H1.
  assumption.

  simplify.
  propositional.
  
  left.
  right.
  apply H.
  equality.

  right.
  eapply H2.
  eassumption.
  assumption.
Qed.

Definition fact_correct (original_input : nat) (st : fact_state) : Prop :=
  match st with
  | AnswerIs ans => fact original_input = ans
  | WithAccumulator _ _ => True
  end.

Theorem fact_init_is : forall original_input,
  fact_init original_input = {WithAccumulator original_input 1}.
Proof.
  simplify.
  apply sets_equal; simplify.
  propositional.

  invert H.
  equality.

  rewrite <- H0.
  constructor.
Qed.

Theorem singleton_in : forall {A} (x : A),
  {x} x.
Proof.
  simplify.
  equality.
Qed.

Theorem factorial_ok_2 :
  invariantFor (factorial_sys 2) (fact_correct 2).
Proof.
  simplify.
  eapply invariantFor_weaken.

  apply multiStepClosure_ok.
  simplify.
  rewrite fact_init_is.

  eapply MscStep.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  eapply MscStep.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  eapply MscStep.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  apply MscDone.
  apply prove_oneStepClosure; simplify.
  propositional.
  propositional; invert H0; try equality.
  invert H; equality.
  invert H1; equality.
  invert H; equality.
  invert H; try equality.

  simplify.
  propositional; subst; simplify; propositional.
              (* ^-- *)
Qed.
