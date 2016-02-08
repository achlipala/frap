(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 4: Transition Systems
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.


(* Here's a classic recursive, functional program for factorial. *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => fact n' * S n'
  end.

(* But let's reformulate factorial relationally, as an example to explore
 * treatment of inductive relations in Coq.  First, these are the states of our
 * state machine. *)
Inductive fact_state :=
| AnswerIs (answer : nat)
| WithAccumulator (input accumulator : nat).

(* This *predicate* captures which states are starting states.
 * Before the main colon of [Inductive], we list *parameters*, which stay fixed
 * throughout recursive invocations of a predicate (though this definition does
 * not use recursion).  After the colon, we give a type that expresses which
 * additional arguments exist, followed by [Prop] for "proposition."
 * Putting this inductive definition in [Prop] is what marks at as a predicate.
 * Our prior definitions have implicitly been in [Set], the normal universe
 * of mathematical objects. *)
Inductive fact_init (original_input : nat) : fact_state -> Prop :=
| FactInit : fact_init original_input (WithAccumulator original_input 1).

(** And here are the states where we declare execution complete. *)
Inductive fact_final : fact_state -> Prop :=
| FactFinal : forall ans, fact_final (AnswerIs ans).

(** The most important part: the relation to step between states *)
Inductive fact_step : fact_state -> fact_state -> Prop :=
| FactDone : forall acc,
  fact_step (WithAccumulator O acc) (AnswerIs acc)
| FactStep : forall n acc,
  fact_step (WithAccumulator (S n) acc) (WithAccumulator n (acc * S n)).

(* We care about more than just single steps.  We want to run factorial to
 * completion, for which it is handy to define a general relation of
 * *transitive-reflexive closure*, like so. *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z,
  R x y
  -> trc R y z
  -> trc R x z.

(* Ironically, this definition is not obviously transitive!
 * Let's prove transitivity as a lemma. *)
Theorem trc_trans : forall {A} (R : A -> A -> Prop) x y, trc R x y
  -> forall z, trc R y z
    -> trc R x z.
Proof.
  induct 1; simplify.

  assumption.
  (* [assumption]: prove a conclusion that matches some hypothesis exactly. *)

  eapply TrcFront.
  (* [eapply H]: like [apply], but works when it is not obvious how to
   *   instantiate the quantifiers of theorem/hypothesis [H].  Instead,
   *   placeholders are inserted for those quantifiers, to be determined
   *   later. *)
  eassumption.
  (* [eassumption]: prove a conclusion that matches some hypothesis, when we
   *   choose the right clever instantiation of placeholders.  Those placehoders
   *   are then replaced everywhere with their new values. *)
  apply IHtrc.
  assumption.
  (* [assumption]: like [eassumption], but never figures out placeholder
   *   values. *)
Qed.

(* Transitive-reflexive closure is so common that it deserves a shorthand notation! *)
Notation "R ^*" := (trc R) (at level 0).

(* Now let's use it to execute the factorial program. *)
Example factorial_3 : fact_step^* (WithAccumulator 3 1) (AnswerIs 6).
Proof.
  eapply TrcFront.
  apply FactStep.
  simplify.
  eapply TrcFront.
  apply FactStep.
  simplify.
  eapply TrcFront.
  apply FactStep.
  simplify.
  eapply TrcFront.
  apply FactDone.
  apply TrcRefl.
Qed.

(* That was exhausting yet uninformative.  We can use a different tactic to blow
 * through such obvious proof trees. *)
Example factorial_3_auto : fact_step^* (WithAccumulator 3 1) (AnswerIs 6).
Proof.
  repeat econstructor.
  (* [econstructor]: tries all declared rules of the predicate in the
   *   conclusion, attempting each with [eapply] until one works. *)

  (* Note that here [econstructor] is doing double duty, applying the rules of
   * both [trc] and [fact_step]. *)
Qed.

(* To prove that our state machine is correct, we rely on the crucial technique
 * of *invariants*.  What is an invariant?  Here's a general definition, in
 * terms of an arbitrary *transition system* defined by a set of states,
 * an initial-state relation, and a step relation. *)
Definition invariantFor {state} (initial : state -> Prop) (step : state -> state -> Prop) (invariant : state -> Prop) :=
  forall s, initial s
            -> forall s', step^* s s'
                          -> invariant s'.
(* That is, when we begin in an initial state and take any number of steps, the
 * place we wind up always satisfied the invariant. *)

(* Here's a simple lemma to help us apply an invariant usefully,
 * really just restating the definition. *)
Theorem use_invariant : forall {state} (initial : state -> Prop)
  (step : state -> state -> Prop) (invariant : state -> Prop) s s',
  step^* s s'
  -> initial s
  -> invariantFor initial step invariant
  -> invariant s'.
Proof.
  unfold invariantFor.
  simplify.
  eapply H1.
  eassumption.
  assumption.
Qed.

(* What's the most fundamental way to establish an invariant?  Induction! *)
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

(* Here's a good invariant for factorial, parameterized on the original input
 * to the program. *)
Definition fact_invariant (original_input : nat) (st : fact_state) : Prop :=
  match st with
  | AnswerIs ans => fact original_input = ans
  | WithAccumulator n acc => fact original_input = fact n * acc
  end.

(* We can use [invariant_induction] to prove that it really is a good
 * invariant. *)
Theorem fact_invariant_ok : forall original_input,
  invariantFor (fact_init original_input) fact_step (fact_invariant original_input).
Proof.
  simplify.
  apply invariant_induction; simplify.

  (* Step 1: invariant holds at the start. (base case) *)
  (* We have a hypothesis establishing [fact_init original_input s].
   * By inspecting the definition of [fact_init], we can draw conclusions about
   * what [s] must be.  The [invert] tactic formalizes that intuition,
   * replacing a hypothesis with certain "obvious inferences" from the original.
   * In general, when multiple different rules may have been used to conclude a
   * fact, [invert] may generate one new subgoal per eligible rule, but here the
   * predicate is only defined with one rule. *)
  invert H.
  (* We magically learn [s = WithAccumulator original_input 1]! *)
  simplify.
  ring.

  (* Step 2: steps preserve the invariant. (induction step) *)
  invert H0.
  (* This time, [invert] is used on a predicate with two rules, neither of which
   * can be ruled out for this case, so we get two subgoals from one. *)

  simplify.
  linear_arithmetic.

  simplify.
  rewrite H.
  ring.
Qed.
