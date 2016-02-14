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
  apply oneStepClosure_empty.
  simplify.

  apply MscDone.
  apply prove_oneStepClosure; simplify.
  propositional.
  propositional; invert H0; try equality.
  invert H; equality.
  invert H1; equality.

  simplify.
  propositional; subst; simplify; propositional.
              (* ^-- *)
Qed.

Hint Rewrite fact_init_is.

Ltac model_check_done :=
  apply MscDone; apply prove_oneStepClosure; simplify; propositional; subst;
  repeat match goal with
         | [ H : _ |- _ ] => invert H
         end; simplify; equality.

Ltac model_check_step :=
  eapply MscStep; [
    repeat ((apply oneStepClosure_empty; simplify)
            || (apply oneStepClosure_split; [ simplify;
                                              repeat match goal with
                                                     | [ H : _ |- _ ] => invert H
                                                     end; apply singleton_in | ]))
  | simplify ].

Ltac model_check_steps1 := model_check_done || model_check_step.
Ltac model_check_steps := repeat model_check_steps1.

Ltac model_check_finish := simplify; propositional; subst; simplify; equality.

Ltac model_check_find_invariant :=
  simplify; eapply invariantFor_weaken; [
    apply multiStepClosure_ok; simplify; model_check_steps
  | ].

Ltac model_check := model_check_find_invariant; model_check_finish.

Theorem factorial_ok_2_snazzy :
  invariantFor (factorial_sys 2) (fact_correct 2).
Proof.
  model_check.
Qed.

Theorem factorial_ok_3 :
  invariantFor (factorial_sys 3) (fact_correct 3).
Proof.
  model_check.
Qed.

Theorem factorial_ok_4 :
  invariantFor (factorial_sys 4) (fact_correct 4).
Proof.
  model_check.
Qed.


(** * Getting smarter about not exploring from the same state twice *)

(*Theorem oneStepClosure_new_done : forall state (sys : trsys state) (invariant : state -> Prop),
  (forall st, sys.(Initial) st -> invariant st)
  -> oneStepClosure_new sys invariant invariant
  -> invariantFor sys invariant.
Proof.
  unfold oneStepClosure_new.
  propositional.
  apply invariant_induction.
  assumption.
  simplify.
  eapply H2.
  eassumption.
  assumption.
Qed.*)

Inductive multiStepClosure_smarter {state} (sys : trsys state)
  : (state -> Prop) -> (state -> Prop) -> (state -> Prop) -> Prop :=
| MscsDone : forall inv worklist,
    oneStepClosure sys inv inv
    -> multiStepClosure_smarter sys inv worklist inv
| MscsStep : forall inv worklist inv' inv'',
    oneStepClosure_new sys worklist inv'
    -> multiStepClosure_smarter sys (inv \cup inv') (inv' \setminus inv) inv''
    -> multiStepClosure_smarter sys inv worklist inv''.

Lemma multiStepClosure_smarter_ok' : forall state (sys : trsys state)
  (inv worklist inv' : state -> Prop),
  multiStepClosure_smarter sys inv worklist inv'
  -> (forall st, sys.(Initial) st -> inv st)
  -> invariantFor sys inv'.
Proof.
  induct 1; simplify.

  apply oneStepClosure_done.
  assumption.
  assumption.

  apply IHmultiStepClosure_smarter.
  simplify.
  left.
  apply H1.
  assumption.
Qed.

Theorem multiStepClosure_smarter_ok : forall state (sys : trsys state) (inv : state -> Prop),
  multiStepClosure_smarter sys sys.(Initial) sys.(Initial) inv
  -> invariantFor sys inv.
Proof.
  simplify.
  eapply multiStepClosure_smarter_ok'.
  eassumption.
  propositional.
Qed.

Theorem oneStepClosure_new_empty : forall state (sys : trsys state),
  oneStepClosure_new sys (constant nil) (constant nil).
Proof.
  unfold oneStepClosure_new; propositional.
Qed.

Theorem oneStepClosure_new_split : forall state (sys : trsys state) st sts (inv1 inv2 : state -> Prop),
  (forall st', sys.(Step) st st' -> inv1 st')
  -> oneStepClosure_new sys (constant sts) inv2
  -> oneStepClosure_new sys (constant (st :: sts)) (inv1 \cup inv2).
Proof.
  unfold oneStepClosure_new; propositional.

  invert H1.

  left.
  apply H.
  assumption.

  right.
  eapply H0.
  eassumption.
  assumption.
Qed.

Theorem factorial_ok_2_smarter :
  invariantFor (factorial_sys 2) (fact_correct 2).
Proof.
  simplify.
  eapply invariantFor_weaken.

  apply multiStepClosure_smarter_ok.
  simplify.

  eapply MscsStep.
  apply oneStepClosure_new_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_new_empty.
  simplify.

  eapply MscsStep.
  apply oneStepClosure_new_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  eapply MscsStep.
  apply oneStepClosure_new_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  apply MscsDone.
  apply prove_oneStepClosure; simplify.
  propositional.
  propositional; invert H0; try equality.
  invert H; equality.
  invert H1; equality.

  simplify.
  propositional; subst; simplify; propositional.
Qed.

Ltac smodel_check_done :=
  apply MscsDone; apply prove_oneStepClosure; simplify; propositional; subst;
  repeat match goal with
         | [ H : _ |- _ ] => invert H
         end; simplify; equality.

Ltac smodel_check_step :=
  eapply MscsStep; [
    repeat ((apply oneStepClosure_new_empty; simplify)
            || (apply oneStepClosure_new_split; [ simplify;
                                                  repeat match goal with
                                                         | [ H : _ |- _ ] => invert H
                                                         end; apply singleton_in | ]))
  | simplify ].

Ltac smodel_check_steps1 := smodel_check_done || smodel_check_step.
Ltac smodel_check_steps := repeat smodel_check_steps1.

Ltac smodel_check_find_invariant :=
  simplify; eapply invariantFor_weaken; [
    apply multiStepClosure_smarter_ok; simplify; smodel_check_steps
  | ].

Ltac smodel_check := smodel_check_find_invariant; model_check_finish.

Theorem factorial_ok_2_smarter_snazzy :
  invariantFor (factorial_sys 2) (fact_correct 2).
Proof.
  smodel_check.
Qed.

Theorem factorial_ok_3_smarter_snazzy :
  invariantFor (factorial_sys 3) (fact_correct 3).
Proof.
  smodel_check.
Qed.

Theorem factorial_ok_5_smarter_snazzy :
  invariantFor (factorial_sys 5) (fact_correct 5).
Proof.
  smodel_check.
Qed.
