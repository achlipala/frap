(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 5: Transition Systems
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

(* A useful general notion for transition systems: reachable states *)
Inductive reachable {state} (sys : trsys state) (st : state) : Prop :=
| Reachable : forall st0,
  sys.(Initial) st0
  -> sys.(Step)^* st0 st
  -> reachable sys st.

(* To prove that our state machine is correct, we rely on the crucial technique
 * of *invariants*.  What is an invariant?  Here's a general definition, in
 * terms of an arbitrary transition system. *)
Definition invariantFor {state} (sys : trsys state) (invariant : state -> Prop) :=
  forall s, sys.(Initial) s
            -> forall s', sys.(Step)^* s s'
                          -> invariant s'.
(* That is, when we begin in an initial state and take any number of steps, the
 * place we wind up always satisfies the invariant. *)

(* Here's a simple lemma to help us apply an invariant usefully,
 * really just restating the definition. *)
Lemma use_invariant' : forall {state} (sys : trsys state)
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

Theorem use_invariant : forall {state} (sys : trsys state)
  (invariant : state -> Prop) s,
  invariantFor sys invariant
  -> reachable sys s
  -> invariant s.
Proof.
  simplify.
  invert H0.
  eapply use_invariant'.
  eassumption.
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
  (* [propositional]: simplify the goal according to the rules of propositional
   *   logic. *)

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
Theorem fact_invariant_always : forall original_input s,
  reachable (factorial_sys original_input) s
  -> fact_invariant original_input s.
Proof.
  simplify.
  eapply use_invariant.
  apply fact_invariant_ok.
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

Theorem fact_ok : forall original_input s,
  reachable (factorial_sys original_input) s
  -> fact_final s
  -> s = AnswerIs (fact original_input).
Proof.
  simplify.
  apply fact_ok'.
  assumption.
  apply fact_invariant_always.
  assumption.
Qed.


(** * A simple example of another program as a state transition system *)

(* We'll formalize this pseudocode for one thread of a concurrent, shared-memory program.
  lock();
  local = global;
  global = local + 1;
  unlock();
*)

(* This inductive state effectively encodes all possible combinations of two
 * kinds of *local*state* in a thread:
 * - program counter
 * - values of local variables that may be read eventually *)
Inductive increment_program :=
| Lock
| Read
| Write (local : nat)
| Unlock
| Done.

(* Next, a type for state shared between threads. *)
Record inc_state := {
  Locked : bool; (* Does a thread hold the lock? *)
  Global : nat   (* A shared counter *)
}.

(* The combined state, from one thread's perspective, using a general
 * definition. *)
Record threaded_state shared private := {
  Shared : shared;
  Private : private
}.

Definition increment_state := threaded_state inc_state increment_program.

(* Now a routine definition of the three key relations of a transition system.
 * The most interesting logic surrounds saving the counter value in the local
 * state after reading. *)

Inductive increment_init : increment_state -> Prop :=
| IncInit :
  increment_init {| Shared := {| Locked := false; Global := O |};
                    Private := Lock |}.

Inductive increment_step : increment_state -> increment_state -> Prop :=
| IncLock : forall g,
  increment_step {| Shared := {| Locked := false; Global := g |};
                    Private := Lock |}
                 {| Shared := {| Locked := true; Global := g |};
                    Private := Read |}
| IncRead : forall l g,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Read |}
                 {| Shared := {| Locked := l; Global := g |};
                    Private := Write g |}
| IncWrite : forall l g v,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Write v |}
                 {| Shared := {| Locked := l; Global := S v |};
                    Private := Unlock |}
| IncUnlock : forall l g,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Unlock |}
                 {| Shared := {| Locked := false; Global := g |};
                    Private := Done |}.

Definition increment_sys := {|
  Initial := increment_init;
  Step := increment_step
|}.


(** * Running transition systems in parallel *)

(* That last example system is a cop-out: it only runs a single thread.  We want
 * to run several threads in parallel, sharing the global state.  Here's how we
 * can do it for just two threads.  The key idea is that, while in the new
 * system the type of shared state remains the same, we take the Cartesian
 * product of the sets of private state. *)

Inductive parallel_init shared private1 private2
  (init1 : threaded_state shared private1 -> Prop)
  (init2 : threaded_state shared private2 -> Prop)
  : threaded_state shared (private1 * private2) -> Prop :=
| Pinit : forall sh pr1 pr2,
  init1 {| Shared := sh; Private := pr1 |}
  -> init2 {| Shared := sh; Private := pr2 |}
  -> parallel_init init1 init2 {| Shared := sh; Private := (pr1, pr2) |}.

Inductive parallel_step shared private1 private2
          (step1 : threaded_state shared private1 -> threaded_state shared private1 -> Prop)
          (step2 : threaded_state shared private2 -> threaded_state shared private2 -> Prop)
          : threaded_state shared (private1 * private2)
            -> threaded_state shared (private1 * private2) -> Prop :=
| Pstep1 : forall sh pr1 pr2 sh' pr1',
  (* First thread gets to run. *)
  step1 {| Shared := sh; Private := pr1 |} {| Shared := sh'; Private := pr1' |}
  -> parallel_step step1 step2 {| Shared := sh; Private := (pr1, pr2) |}
               {| Shared := sh'; Private := (pr1', pr2) |}
| Pstep2 : forall sh pr1 pr2 sh' pr2',
  (* Second thread gets to run. *)
  step2 {| Shared := sh; Private := pr2 |} {| Shared := sh'; Private := pr2' |}
  -> parallel_step step1 step2 {| Shared := sh; Private := (pr1, pr2) |}
               {| Shared := sh'; Private := (pr1, pr2') |}.

Definition parallel shared private1 private2
           (sys1 : trsys (threaded_state shared private1))
           (sys2 : trsys (threaded_state shared private2)) := {|
  Initial := parallel_init sys1.(Initial) sys2.(Initial);
  Step := parallel_step sys1.(Step) sys2.(Step)
|}.

(* Example: composing two threads of the kind we formalized earlier *)
Definition increment2_sys := parallel increment_sys increment_sys.

(* Let's prove that the counter is always 2 when the composed program terminates. *)

(* First big idea: the program counter of a thread tells us how much it has
 * added to the shared counter so far. *)
Definition contribution_from (pr : increment_program) : nat :=
  match pr with
  | Unlock => 1
  | Done => 1
  | _ => 0
  end.

(* Second big idea: the program counter also tells us whether a thread holds the lock. *)
Definition has_lock (pr : increment_program) : bool :=
  match pr with
  | Read => true
  | Write _ => true
  | Unlock => true
  | _ => false
  end.

(* Now we see that the shared state is a function of the two program counters,
 * as follows. *)
Definition shared_from_private (pr1 pr2 : increment_program) :=
  {| Locked := has_lock pr1 || has_lock pr2;
     Global := contribution_from pr1 + contribution_from pr2 |}.

(* We also need a condition to formalize compatibility between program counters,
 * e.g. that they shouldn't both be in the critical section at once. *)
Definition instruction_ok (self other : increment_program) :=
  match self with
  | Lock => True
  | Read => has_lock other = false
  | Write n => has_lock other = false /\ n = contribution_from other
  | Unlock => has_lock other = false
  | Done => True
  end.

(** Now we have the ingredients to state the invariant. *)
Inductive increment2_invariant :
  threaded_state inc_state (increment_program * increment_program) -> Prop :=
| Inc2Inv : forall pr1 pr2,
  instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> increment2_invariant {| Shared := shared_from_private pr1 pr2; Private := (pr1, pr2) |}.

(** It's convenient to prove this alternative equality-based "constructor" for the invariant. *)
Lemma Inc2Inv' : forall sh pr1 pr2,
  sh = shared_from_private pr1 pr2
  -> instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> increment2_invariant {| Shared := sh; Private := (pr1, pr2) |}.
Proof.
  intros.
  rewrite H.
  apply Inc2Inv; assumption.
Qed.

(* Now, to show it really is an invariant. *)
Theorem increment2_invariant_ok : invariantFor increment2_sys increment2_invariant.
Proof.
  apply invariant_induction; simplify.

  invert H.
  invert H0.
  invert H1.
  apply Inc2Inv'.

  unfold shared_from_private.
  simplify.
  equality.

  simplify.
  propositional.

  simplify.
  propositional.

  invert H.
  invert H0.

  invert H6; simplify.

  cases pr2; simplify.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  equality.
  (* Note that [equality] derives a contradiction from [false = true]! *)
  equality.
  equality.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  cases pr2; simplify.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  equality.
  equality.
  equality.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  cases pr2; simplify.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  equality.
  equality.
  equality.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  cases pr2; simplify.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  equality.
  equality.
  equality.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.


  invert H6.

  cases pr1; simplify.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  equality.
  (* Note that [equality] derives a contradiction from [false = true]! *)
  equality.
  equality.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  cases pr1; simplify.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  equality.
  (* Note that [equality] derives a contradiction from [false = true]! *)
  equality.
  equality.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  cases pr1; simplify.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  equality.
  (* Note that [equality] derives a contradiction from [false = true]! *)
  equality.
  equality.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  cases pr1; simplify.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.

  equality.
  (* Note that [equality] derives a contradiction from [false = true]! *)
  equality.
  equality.

  apply Inc2Inv'; unfold shared_from_private; simplify.
  equality.
  equality.
  equality.
Qed.

(* We can remove the repetitive proving with a more automated proof script,
 * whose details are beyond the scope of this book, but which may be interesting
 * anyway! *)
Theorem increment2_invariant_ok_snazzy : invariantFor increment2_sys increment2_invariant.
Proof.
  apply invariant_induction; simplify;
  repeat match goal with
         | [ H : increment2_invariant _ |- _ ] => invert H
         | [ H : parallel_init _ _ _ |- _ ] => invert H
         | [ H : increment_init _ |- _ ] => invert H
         | [ H : parallel_step _ _ _ _ |- _ ] => invert H
         | [ H : increment_step _ _ |- _ ] => invert H
         | [ pr : increment_program |- _ ] => cases pr; simplify
         end; try equality;
  apply Inc2Inv'; unfold shared_from_private; simplify; equality.
Qed.

(* Now, to prove our final result about the two incrementing threads, let's use
 * a more general fact, about when one invariant implies another. *)
Theorem invariant_weaken : forall {state} (sys : trsys state)
  (invariant1 invariant2 : state -> Prop),
  invariantFor sys invariant1
  -> (forall s, invariant1 s -> invariant2 s)
  -> invariantFor sys invariant2.
Proof.
  unfold invariantFor; simplify.
  apply H0.
  eapply H.
  eassumption.
  assumption.
Qed.

(* Here's another, much weaker invariant, corresponding exactly to the overall
 * correctness property we want to establish for this system. *)
Definition increment2_right_answer
  (s : threaded_state inc_state (increment_program * increment_program)) :=
  s.(Private) = (Done, Done)
  -> s.(Shared).(Global) = 2.

(** Now we can prove that the system only runs to happy states. *)
Theorem increment2_sys_correct : forall s,
  reachable increment2_sys s
  -> increment2_right_answer s.
Proof.
  simplify.
  eapply use_invariant.
  apply invariant_weaken with (invariant1 := increment2_invariant).
  (* Note the use of a [with] clause to specify a quantified variable's
   * value. *)

  apply increment2_invariant_ok.

  simplify.
  invert H0.
  unfold increment2_right_answer; simplify.
  invert H0.
  (* Here we use inversion on an equality, to derive more primitive
   * equalities. *)
  simplify.
  equality.

  assumption.
Qed.
