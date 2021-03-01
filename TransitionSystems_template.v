(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 6: Transition Systems
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

(* *Initial* states *)
Inductive fact_init (original_input : nat) : fact_state -> Prop :=
| FactInit : fact_init original_input (WithAccumulator original_input 1).

(** *Final* states *)
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

(* Transitive-reflexive closure is so common that it deserves a shorthand notation! *)
Set Warnings "-notation-overridden". (* <-- needed while we play with defining one
                                      * of the book's notations ourselves locally *)
Notation "R ^*" := (trc R) (at level 0).

(* Now let's use it to execute the factorial program. *)
Example factorial_3 : fact_step^* (WithAccumulator 3 1) (AnswerIs 6).
Proof.
Admitted.

(* It will be useful to give state machines more first-class status, as
 * *transition systems*, formalized by this record type.  It has one type
 * parameter, [state], which records the type of states. *)
Record trsys state := {
  Initial : state -> Prop;
  Step : state -> state -> Prop
}.

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

Definition fact_invariant (original_input : nat) (st : fact_state) : Prop :=
  True.
(* We must fill in a better invariant. *)

Theorem fact_invariant_ok : forall original_input,
  invariantFor (factorial_sys original_input) (fact_invariant original_input).
Proof.
Admitted.

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
Admitted.

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

(** We must write an invariant. *)
Inductive increment2_invariant :
  threaded_state inc_state (increment_program * increment_program) -> Prop :=
| Inc2Inv : forall sh pr1 pr2,
  increment2_invariant {| Shared := sh; Private := (pr1, pr2) |}.
(* This isn't it yet! *)

(* Now, to show it really is an invariant. *)
Theorem increment2_invariant_ok : invariantFor increment2_sys increment2_invariant.
Proof.
Admitted.

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
Admitted.
(*simplify.
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
Qed.*)
