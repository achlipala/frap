(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 4: Transition Systems
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.
(* This command will treat type arguments to functions as implicit, like in
 * Haskell or ML. *)


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
  (* Note how we pass a *number* to [induct], to ask for induction on
   * *the first hypothesis in the theorem statement*. *)

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

(* It will be useful to give state machines more first-class status, as
 * *transition systems*, formalized by this record type.  It has one type
 * parameter, [state], which records the type of states. *)
Record trsys state := {
  Initial : state -> Prop;
  Step : state -> state -> Prop
}.
(* Probably it's intuitively clear what a record type must be.
 * See usage examples below to fill in more of the details.
 * Note that [state] is a polymorphic type parameter. *)

(* The example of our factorial program: *)
Definition factorial_sys (original_input : nat) : trsys fact_state := {|
  Initial := fact_init original_input;
  Step := fact_step
|}.

(* To prove that our state machine is correct, we rely on the crucial technique
 * of *invariants*.  What is an invariant?  Here's a general definition, in
 * terms of an arbitrary *transition system* defined by a set of states,
 * an initial-state relation, and a step relation. *)
Definition invariantFor {state} (sys : trsys state) (invariant : state -> Prop) :=
  forall s, sys.(Initial) s
            -> forall s', sys.(Step)^* s s'
                          -> invariant s'.
(* That is, when we begin in an initial state and take any number of steps, the
 * place we wind up always satisfies the invariant. *)

(* Here's a simple lemma to help us apply an invariant usefully,
 * really just restating the definition. *)
Theorem use_invariant : forall {state} (sys : trsys state)
  (invariant : state -> Prop) s s',
  invariantFor sys invariant
  -> sys.(Initial) s
  -> sys.(Step)^* s s'
  -> invariant s'.
Proof.
  unfold invariantFor.
  simplify.
  eapply H.
  eassumption.
  assumption.
Qed.

(* What's the most fundamental way to establish an invariant?  Induction! *)
Lemma invariant_induction' : forall {state} (sys : trsys state)
  (invariant : state -> Prop),
  (forall s, invariant s -> forall s', sys.(Step) s s' -> invariant s')
  -> forall s s', sys.(Step)^* s s'
     -> invariant s
     -> invariant s'.
Proof.
  induct 2; propositional.

  apply IHtrc.
  eapply H.
  eassumption.
  assumption.
Qed.

Theorem invariant_induction : forall {state} (sys : trsys state)
  (invariant : state -> Prop),
  (forall s, sys.(Initial) s -> invariant s)
  -> (forall s, invariant s -> forall s', sys.(Step) s s' -> invariant s')
  -> invariantFor sys invariant.
Proof.
  unfold invariantFor; intros.
  eapply invariant_induction'.
  eassumption.
  eassumption.
  apply H.
  assumption.
Qed.

(* That's enough abstract results for now.  Let's apply them to our example.
 * Here's a good invariant for factorial, parameterized on the original input
 * to the program. *)
Definition fact_invariant (original_input : nat) (st : fact_state) : Prop :=
  match st with
  | AnswerIs ans => fact original_input = ans
  | WithAccumulator n acc => fact original_input = fact n * acc
  end.

(* We can use [invariant_induction] to prove that it really is a good
 * invariant. *)
Theorem fact_invariant_ok : forall original_input,
  invariantFor (factorial_sys original_input) (fact_invariant original_input).
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

(* Therefore, every reachable state satisfies this invariant. *)
Theorem fact_invariant_always : forall original_input s s',
  (factorial_sys original_input).(Step)^* s s'
  -> (factorial_sys original_input).(Initial) s
  -> fact_invariant original_input s'.
Proof.
  simplify.
  eapply use_invariant.
  apply fact_invariant_ok.
  eassumption.
  assumption.
Qed.

(* Therefore, any final state has the right answer! *)
Lemma fact_ok' : forall original_input s,
  fact_final s
  -> fact_invariant original_input s
  -> s = AnswerIs (fact original_input).
Proof.
  invert 1; simplify; equality.
Qed.

Theorem fact_ok : forall original_input s s',
  (factorial_sys original_input).(Step)^* s s'
  -> (factorial_sys original_input).(Initial) s
  -> fact_final s'
  -> s' = AnswerIs (fact original_input).
Proof.
  simplify.
  apply fact_ok'.
  assumption.
  eapply fact_invariant_always.
  eassumption.
  assumption.
Qed.
