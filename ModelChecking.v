(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 6: Model Checking
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Set Warnings "-notation-overridden". (* <-- needed while we play with defining one
                                      * of the book's notations ourselves locally *)
Require Import Frap TransitionSystems.

Set Implicit Arguments.


(* Coming up with invariants ourselves can be tedious!  Let's investigate how we
 * can automate the choice of invariants, for systems with only finitely many
 * reachable states.  This style is known as model checking.  First, let's think
 * more deliberately about how to grow a candidate invariant by adding new cases
 * that we missed.  Here's what it means for one invariant to retain all cases of
 * another. *)
Definition oneStepClosure_current {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  forall st, invariant1 st
             -> invariant2 st.

(* And here's what it means to add all new states reachable from the original
 * set. *)
Definition oneStepClosure_new {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  forall st st', invariant1 st
                 -> sys.(Step) st st'
                 -> invariant2 st'.

(* Putting together the two conditions, we have a closure operator, for
 * enriching a candidate invariant with all new states reachable from it in a
 * single step. *)
Definition oneStepClosure {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  oneStepClosure_current sys invariant1 invariant2
  /\ oneStepClosure_new sys invariant1 invariant2.

(* Here's a simple restatement of [oneStepClosure] as a theorem with two
 * premises. *)
Theorem prove_oneStepClosure : forall state (sys : trsys state) (inv1 inv2 : state -> Prop),
  (forall st, inv1 st -> inv2 st)
  -> (forall st st', inv1 st -> sys.(Step) st st' -> inv2 st')
  -> oneStepClosure sys inv1 inv2.
Proof.
  unfold oneStepClosure.
  propositional.
Qed.

(* Now imagine the following general procedure to find an invariant.  Start with
 * the initial states as the candidate invariant.  Now take the one-step
 * closure, adding all states reachable in one step.  Then take it again, and
 * again, until the invariant is "big enough."  What is the formal meaning of
 * this termination condition?  We are done if one-step closure brings us back
 * to the original set.  (Of course, we must also retain all the initial
 * states.) *)
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

(* Now we define an inductive relation, capturing repeated closure until
 * convergence. *)
Inductive multiStepClosure {state} (sys : trsys state)
  : (state -> Prop) -> (state -> Prop) -> Prop :=

(* We might be done, if one-step closure has no effect. *)
| MscDone : forall inv,
    oneStepClosure sys inv inv
    -> multiStepClosure sys inv inv

(* Or we might need to run another one-step closure and recurse. *)
| MscStep : forall inv inv' inv'',
    oneStepClosure sys inv inv'
    -> multiStepClosure sys inv' inv''
    -> multiStepClosure sys inv inv''.

(* Now, with the help of a lemma, we prove that multi-step closure is a sound
 * way to find an invariant for any transition system.  Note that we really do
 * not have that silver bullet here, because, for many systems, multi-step
 * closure does not terminate!  However, if it does, we get a correct
 * invariant. *)

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
  unfold oneStepClosure, oneStepClosure_current in *.
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

(* OK, great.  We know how to find invariants if we can evaluate one-step
 * closure efficiently.  Here's one case that is particularly easy to evaluate,
 * starting from the empty set as the invariant.  We use a function [constant]
 * from the FRAP library, for sets of finite size.  In general, we write
 * [constant [x1; ..., xN]] for the set [{x1, ..., xN}], and in fact the latter
 * notation is available, too. *)
Theorem oneStepClosure_empty : forall state (sys : trsys state),
  oneStepClosure sys (constant nil) (constant nil).
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new; propositional.
Qed.

(* In general, for finite sets, we'll compute one-step closure by closing
 * separately over each element of the set.  This theorem implements one step of
 * that process, where we learn that [inv1] accurately captures where we might
 * get from state [st] in one step.  States [sts] are those left over to
 * consider. *)
Theorem oneStepClosure_split : forall state (sys : trsys state) st sts (inv1 inv2 : state -> Prop),
  (forall st', sys.(Step) st st' -> inv1 st')
  -> oneStepClosure sys (constant sts) inv2
  -> oneStepClosure sys (constant (st :: sts)) ({st} \cup inv1 \cup inv2).
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new; propositional.

  invert H0.

  left.
  (* [left] and [right]: prove a disjunction by proving the left or right case,
   *   respectively.  Note that here, we are using the fact that set union
   *   [\cup] is defined in terms of disjunction. *)
  left.
  simplify.
  propositional.

  right.
  apply H1.
  assumption.

  simplify.
  propositional.
  
  right.
  left.
  apply H.
  equality.

  right.
  right.
  eapply H2.
  eassumption.
  assumption.
Qed.

(* A trivial fact about union and singleton sets.
 * Note that we model sets as functions that are passed elements, deciding in
 * each case whether that element belongs to the set. *)
Theorem singleton_in : forall {A} (x : A) rest,
  ({x} \cup rest) x.
Proof.
  simplify.
  left.
  simplify.
  equality.
Qed.

(* OK, back to our example from last chapter, of factorial as a transition
 * system.  Here's a good overall correctness condition, which we didn't bother
 * to state before. *)
Definition fact_correct (original_input : nat) (st : fact_state) : Prop :=
  match st with
  | AnswerIs ans => fact original_input = ans
  | WithAccumulator _ _ => True
  end.

(* Let's also restate the initial-states set using a singleton set. *)
Theorem fact_init_is : forall original_input,
  fact_init original_input = {WithAccumulator original_input 1}.
Proof.
  simplify.
  apply sets_equal; simplify.
  (* Note the use of a theorem [sets_equal], saying that sets are equal if they
   * have the same elements. *)
  propositional.

  invert H.
  equality.

  rewrite <- H0.
  constructor.
Qed.

(* Now we will prove that factorial is correct, for the input 2, without needing
 * to write out an inductive invariant ourselves.  Note that it's important that
 * we choose a small, constant input, so that the reachable state space is
 * finite and tractable. *)
Theorem factorial_ok_2 :
  invariantFor (factorial_sys 2) (fact_correct 2).
Proof.
  simplify.
  eapply invariant_weaken.
  (* We begin like in last chapter, by strengthening to an inductive
   * invariant. *)

  apply multiStepClosure_ok.
  (* The difference is that we will use multi-step closure to find the invariant
   * automatically.  Note that the invariant appears as an existential variable,
   * whose name begins with a question mark. *)
  simplify.
  rewrite fact_init_is.
  (* It's important to phrase the current candidate invariant explicitly as a
   * finite set, before continuing.  Otherwise, it won't be obvious how to take
   * the one-step closure. *)

  (* Compute which states are reachable after one step. *)
  eapply MscStep.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  (* Compute which states are reachable after two steps. *)
  eapply MscStep.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  (* Compute which states are reachable after three steps. *)
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

  (* Now the candidate invariant is closed under single steps.  Let's prove
   * it. *)
  apply MscDone.
  apply prove_oneStepClosure; simplify.
  propositional.
  propositional; invert H0; try equality.
  invert H; equality.
  invert H1; equality.

  (* Finally, we prove that our new invariant implies the simpler, noninductive
   * one that we started with. *)
  simplify.
  propositional; subst; simplify; propositional.
  (* [subst]: remove all hypotheses like [x = e] for variables [x], simply
   *   replacing all uses of [x] by [e]. *)
Qed.

(* That process was so rote that we can automate it all, in a generic way that
 * will work for most transition systems that have finitely many reachable
 * states.  Here is a definition of some tactics to do the work.
 * BEGIN CODE THAT WILL NOT BE EXPLAINED IN DETAIL! *)

Hint Rewrite fact_init_is.

Ltac model_check_done :=
  apply MscDone; apply prove_oneStepClosure; simplify; propositional; subst;
  repeat match goal with
         | [ H : _ |- _ ] => invert H
         end; simplify; equality.

Theorem singleton_in_other : forall {A} (x : A) (s1 s2 : set A),
  s2 x
  -> (s1 \cup s2) x.
Proof.
  simplify.
  right.
  right.
  assumption.
Qed.

Ltac singletoner :=
  repeat match goal with
         | [ |- _ ?S ] => idtac S; apply singleton_in
         | [ |- (_ \cup _) _ ] => apply singleton_in_other
         end.

Ltac model_check_step0 :=
  eapply MscStep; [
    repeat ((apply oneStepClosure_empty; simplify)
            || (apply oneStepClosure_split; [ simplify;
                                              repeat match goal with
                                                     | [ H : _ |- _ ] => invert H; try congruence
                                                     end; solve [ singletoner ] | ]))
  | simplify ].

Ltac model_check_step :=
  match goal with
  | [ |- multiStepClosure _ ?inv1 _ ] =>
    model_check_step0;
    match goal with
    | [ |- multiStepClosure _ ?inv2 _ ] =>
      (assert (inv1 = inv2) by compare_sets; fail 3)
      || idtac
    end
  end.

Ltac model_check_steps1 := model_check_step || model_check_done.
Ltac model_check_steps := repeat model_check_steps1.

Ltac model_check_finish := simplify; propositional; subst; simplify; equality.

Ltac model_check_infer :=
  apply multiStepClosure_ok; simplify; model_check_steps.

Ltac model_check_find_invariant :=
  simplify; eapply invariant_weaken; [ model_check_infer | ]; cbv beta in *.

Ltac model_check := model_check_find_invariant; model_check_finish.

(* END CODE THAT WILL NOT BE EXPLAINED IN DETAIL! *)

(* Now watch this.  We can check various instances of factorial
 * automatically.  Notice that reachable states are printed as we encounter them
 * in exploration, using [idtac] invocations above.  This printing is for the
 * user's understanding and has no logical meaning. *)

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

Theorem factorial_ok_5 :
  invariantFor (factorial_sys 5) (fact_correct 5).
Proof.
  model_check.
Qed.

(* Let's see that last one broken into two steps, so that we get a look at the
 * inferred invariant. *)
Theorem factorial_ok_5_again :
  invariantFor (factorial_sys 5) (fact_correct 5).
Proof.
  model_check_find_invariant.
  model_check_finish.
Qed.


(** * Abstraction *)

(* It's lovely when we happen to be analyzing a system with a finite state
 * space, but usually we aren't that lucky.  For instance, imagine that we are
 * using a programming language with infinite-precision integers, and we want to
 * check this program:
 * <<
   int global = 0;
 
   thread() {
     int local;

     while (true) {
       local = global;
       global = local + 2;
     }
   }
   >>
 * The program loops indefinitely, adding 2 to a global variable.  We want to
 * prove that "global" always holds an even value.  Here's how we can formalize
 * evenness inductively. *)

Inductive isEven : nat -> Prop :=
| EvenO : isEven 0
| EvenSS : forall n, isEven n -> isEven (S (S n)).

(* And now we define a transition system for the program, in a process that
 * should be routine by now.  We use last chapter's concept of a multithreaded
 * transition system. *)

Inductive add2_thread :=
| Read
| Write (local : nat).

Inductive add2_init : threaded_state nat add2_thread -> Prop :=
| Add2Init : add2_init {| Shared := 0; Private := Read |}.

Inductive add2_step : threaded_state nat add2_thread -> threaded_state nat add2_thread -> Prop :=
| StepRead : forall global,
    add2_step {| Shared := global; Private := Read |}
              {| Shared := global; Private := Write global |}
| StepWrite : forall global local,
    add2_step {| Shared := global; Private := Write local |}
              {| Shared := S (S local); Private := Read |}.

Definition add2_sys1 := {|
  Initial := add2_init;
  Step := add2_step
|}.

Definition add2_sys := parallel add2_sys1 add2_sys1.

(* Here is the invariant we want to prove. *)
Definition add2_correct (st : threaded_state nat (add2_thread * add2_thread)) :=
  isEven st.(Shared).

(* We can't model-check [add2_sys] directly, because it can reach infinitely
 * many states.  Even if we worked with fixed-precision integers, say with 64
 * bits, the state space would be impractically large to explore directly.
 * Instead, we will *abstract* this system into another one that retains its
 * essential properties.  In particular, we want to find another transition
 * system that *simulates* this one, in the sense made precise by this
 * definition, where [sys1] will be [add2_sys] for this example. *)
Inductive simulates state1 state2 (R : state1 -> state2 -> Prop)
  (* [R] is a relation connecting the states of the two systems. *)
  (sys1 : trsys state1) (sys2 : trsys state2) : Prop :=
| Simulates :
  (* Every initial state of [sys1] has some matching initial state of [sys2]. *)
  (forall st1, sys1.(Initial) st1
               -> exists st2, R st1 st2
                              /\ sys2.(Initial) st2)

  (* Starting from a pair of related states, every step in [sys1] can be matched
   * in [sys2], to destinations that are also related. *)
  -> (forall st1 st2, R st1 st2
                      -> forall st1', sys1.(Step) st1 st1'
                                      -> exists st2', R st1' st2'
                                                      /\ sys2.(Step) st2 st2')

  -> simulates R sys1 sys2.

(* Given an invariant for [sys2], we now have a generic way of defining an
 * invariant for [sys1], by composing with [R]. *)
Inductive invariantViaSimulation state1 state2 (R : state1 -> state2 -> Prop)
  (inv2 : state2 -> Prop)
  : state1 -> Prop :=
| InvariantViaSimulation : forall st1 st2, R st1 st2
  -> inv2 st2
  -> invariantViaSimulation R inv2 st1.

(* By way of a lemma, let's prove that, given a simulation, any
 * invariant-via-simulation really is an invariant for the original system. *)
Lemma invariant_simulates' : forall state1 state2 (R : state1 -> state2 -> Prop)
  (sys1 : trsys state1) (sys2 : trsys state2),
  (forall st1 st2, R st1 st2
                   -> forall st1', sys1.(Step) st1 st1'
                                   ->  exists st2', R st1' st2'
                                                    /\ sys2.(Step) st2 st2')
  -> forall st1 st1', sys1.(Step)^* st1 st1'
                      -> forall st2, R st1 st2
                                     -> exists st2', R st1' st2'
                                                     /\ sys2.(Step)^* st2 st2'.
Proof.
  induct 2.

  simplify.
  exists st2.
  (* [exists E]: prove [exists x, P(x)] by proving [P(E)]. *)
  propositional.
  constructor.

  simplify.
  eapply H in H2.
  first_order.
  (* [first_order]: simplify first-order logic structure.  Be forewarned: this
   *   one is especially likely to run forever! *)
  apply IHtrc in H2.
  first_order.
  exists x1.
  propositional.
  econstructor.
  eassumption.
  assumption.
  assumption.
Qed.

Theorem invariant_simulates : forall state1 state2 (R : state1 -> state2 -> Prop)
  (sys1 : trsys state1) (sys2 : trsys state2) (inv2 : state2 -> Prop),
  simulates R sys1 sys2
  -> invariantFor sys2 inv2
  -> invariantFor sys1 (invariantViaSimulation R inv2).
Proof.
  simplify.
  invert H.
  unfold invariantFor; simplify.
  apply H1 in H.
  first_order.
  apply invariant_simulates' with (sys2 := sys2) (R := R) (st2 := x) in H3; try assumption.
  first_order.
  unfold invariantFor in H0.
  apply H0 with (s' := x0) in H4; try assumption.
  econstructor.
  eassumption.
  assumption.
Qed.

(* OK, that's a general theory for abstracting a system with another one that
 * simulates it.  What abstraction will work for our example of the two threads
 * and the counter?  Here's another program that has replaced integers with
 * Booleans, where the Boolean is true iff the matching integer is even.
 * <<
    bool global = true;

    thread() {
      bool local;

      while (true) {
        local = global;
        global = local;
      }
    }
   >>
 * We can formalize this program as a transition system, too. *)

Inductive add2_bthread :=
| BRead
| BWrite (local : bool).

Inductive add2_binit : threaded_state bool add2_bthread -> Prop :=
| Add2BInit : add2_binit {| Shared := true; Private := BRead |}.

Inductive add2_bstep : threaded_state bool add2_bthread -> threaded_state bool add2_bthread -> Prop :=
| StepBRead : forall global,
    add2_bstep {| Shared := global; Private := BRead |}
               {| Shared := global; Private := BWrite global |}
| StepBWrite : forall global local,
    add2_bstep {| Shared := global; Private := BWrite local |}
               {| Shared := local; Private := BRead |}.

Definition add2_bsys1 := {|
  Initial := add2_binit;
  Step := add2_bstep
|}.

Definition add2_bsys := parallel add2_bsys1 add2_bsys1.

(* This invariant formalizes the connection between local states of threads, in
 * the original and abstracted systems. *)
Inductive R_private1 : add2_thread -> add2_bthread -> Prop :=
| RpRead : R_private1 Read BRead
| RpWrite : forall n b, (b = true <-> isEven n)
                        -> R_private1 (Write n) (BWrite b).

(* We lift [R_private1] to a relation over whole states. *)
Inductive add2_R : threaded_state nat (add2_thread * add2_thread)
                   -> threaded_state bool (add2_bthread * add2_bthread)
                   -> Prop :=
| Add2_R : forall n b th1 th2 th1' th2',
  (b = true <-> isEven n)
  -> R_private1 th1 th1'
  -> R_private1 th2 th2'
  -> add2_R {| Shared := n; Private := (th1, th2) |}
            {| Shared := b; Private := (th1', th2') |}.

(* Let's also recharacterize the initial states via a singleton set. *)
Theorem add2_init_is :
  parallel_init add2_binit add2_binit = { {| Shared := true; Private := (BRead, BRead) |} }.
Proof.
  simplify.
  apply sets_equal; simplify.
  propositional.

  invert H.
  invert H2.
  invert H4.
  equality.

  invert H0.
  constructor.
  constructor.
  constructor.
Qed.

(* We ask Coq to remember this lemma as a hint, which will be used by the
 * model-checking tactics that we refrain from explaining in detail. *)
Hint Rewrite add2_init_is.

(* Now, let's verify the original system. *)
Theorem add2_ok :
  invariantFor add2_sys add2_correct.
Proof.
  (* First step: strengthen the invariant.  We leave an underscore for the
   * unknown invariant, to be found by model checking. *)
  eapply invariant_weaken with (invariant1 := invariantViaSimulation add2_R _).

  (* One way to find an invariant-by-simulation is to find an invariant for the
   * abstracted system, as this step asks to do. *)
  apply invariant_simulates with (sys2 := add2_bsys).

  (* Now we must prove that the simulation via [add2_R] is valid, which is
   * routine. *)
  constructor; simplify.

  invert H.
  invert H0.
  invert H1.
  exists {| Shared := true; Private := (BRead, BRead) |}; simplify.
  propositional.
  constructor.
  propositional.
  constructor.
  constructor.
  constructor.

  invert H.
  invert H0; simplify.

  invert H7.

  invert H2.
  exists {| Shared := b; Private := (BWrite b, th2') |}.
  propositional.
  constructor.
  propositional.
  constructor.
  propositional.
  assumption.
  constructor.
  constructor.

  invert H2.
  exists {| Shared := b0; Private := (BRead, th2') |}.
  propositional.
  constructor.
  propositional.
  constructor.
  assumption.
  invert H0.
  propositional.
  constructor.
  assumption.
  constructor.
  constructor.

  invert H7.

  invert H3.
  exists {| Shared := b; Private := (th1', BWrite b) |}.
  propositional.
  constructor.
  propositional.
  assumption.
  constructor.
  propositional.
  constructor.
  constructor.

  invert H3.
  exists {| Shared := b0; Private := (th1', BRead) |}.
  propositional.
  constructor.
  propositional.
  constructor.
  assumption.
  invert H0.
  propositional.
  assumption.
  constructor.
  constructor.
  constructor.

  (* OK, we're glad to have that over with!  Such a process could also be
   * automated, but we won't bother doing so here.  However, we are now in a
   * good state, where our model checker can find the invariant
   * automatically. *)
  model_check_infer.
  (* It finds exactly four reachable states.  We finish by showing that they all
   * obey the original invariant. *)

  invert 1. (* Note that this [1] means "first premise below the double
             * line." *)
  invert H0.
  simplify.
  unfold add2_correct.
  simplify.
  propositional; subst.

  invert H.
  propositional.

  invert H1.
  propositional.

  invert H.
  propositional.

  invert H1.
  propositional.
Qed.


(** * Another abstraction example *)

(* Let's try a fancier example of abstraction.  Here's a simple integer
 * function.
 * <<
    f(int n) {
      int i, j;

      i = 0;
      j = 0;
      while (n > 0) {
        i = i + n;
        j = j + n;
        n = n - 1;
      }
    }
   >>
 * We might want to prove that "i" and "j" are always equal at the end.
 * First, we formalize the transition system. *)

Inductive pc :=
| i_gets_0
| j_gets_0
| Loop
| i_add_n
| j_add_n
| n_sub_1
| Done.

Record vars := {
  N : nat;
  I : nat;
  J : nat
}.

Record state := {
  Pc : pc;
  Vars : vars
}.

Inductive initial : state -> Prop :=
| Init : forall vs, initial {| Pc := i_gets_0; Vars := vs |}.

Inductive step : state -> state -> Prop :=
| Step_i_gets_0 : forall n i j,
  step {| Pc := i_gets_0; Vars := {| N := n;
                                     I := i;
                                     J := j |} |}
       {| Pc := j_gets_0; Vars := {| N := n;
                                     I := 0;
                                     J := j |} |}
| Step_j_gets_0 : forall n i j,
  step {| Pc := j_gets_0; Vars := {| N := n;
                                     I := i;
                                     J := j |} |}
       {| Pc := Loop; Vars := {| N := n;
                                 I := i;
                                 J := 0 |} |}
| Step_Loop_done : forall i j,
  step {| Pc := Loop; Vars := {| N := 0;
                                 I := i;
                                 J := j |} |}
       {| Pc := Done; Vars := {| N := 0;
                                 I := i;
                                 J := j |} |}
| Step_Loop_enter : forall n i j,
  step {| Pc := Loop; Vars := {| N := S n;
                                 I := i;
                                 J := j |} |}
       {| Pc := i_add_n; Vars := {| N := S n;
                                    I := i;
                                    J := j |} |}
| Step_i_add_n : forall n i j,
  step {| Pc := i_add_n; Vars := {| N := n;
                                    I := i;
                                    J := j |} |}
       {| Pc := j_add_n; Vars := {| N := n;
                                    I := i + n;
                                    J := j |} |}
| Step_j_add_n : forall n i j,
  step {| Pc := j_add_n; Vars := {| N := n;
                                    I := i;
                                    J := j |} |}
       {| Pc := n_sub_1; Vars := {| N := n;
                                    I := i;
                                    J := j + n |} |}
| Step_n_sub_1 : forall n i j,
  step {| Pc := n_sub_1; Vars := {| N := n;
                                    I := i;
                                    J := j |} |}
       {| Pc := Loop; Vars := {| N := n - 1;
                                 I := i;
                                 J := j |} |}.

Definition loopy_sys := {|
  Initial := initial;
  Step := step
|}.

Definition loopy_correct (st : state) :=
  st.(Pc) = Done -> st.(Vars).(I) = st.(Vars).(J).

(* Which abstraction will give us a finite-state system?  Unlike with factorial,
 * here we are more ambitious, seeking an abstraction that will be finite-state
 * even when considering all possible parameter values "n".  Let's try this
 * simple abstract version of variable state. *)
Inductive absvars :=
| Unknown
  (* We don't know anything about the values of the variables. *)
| i_is_0
  (* We know [i == 0]. *)
| i_eq_j
  (* We know [i == j]. *)
| i_eq_j_plus_n.
  (* We know [i == j + n]. *)

(* To get our abstract states, we keep the same program counters and just change
 * out the variable state. *)
Record absstate := {
  APc : pc;
  AVars : absvars
}.

(* Here's the rather boring new abstract step relation.  Note the clever state
 * transformations, in terms of our new abstraction. *)
Inductive absstep : absstate -> absstate -> Prop :=
| AStep_i_gets_0 : forall vs,
  absstep {| APc := i_gets_0; AVars := vs |}
          {| APc := j_gets_0; AVars := i_is_0 |}
| AStep_j_gets_0_i_is_0 :
  absstep {| APc := j_gets_0; AVars := i_is_0 |}
          {| APc := Loop; AVars := i_eq_j |}
| AStep_j_gets_0_Other : forall vs,
  vs <> i_is_0
  -> absstep {| APc := j_gets_0; AVars := vs |}
             {| APc := Loop; AVars := Unknown |}
| AStep_Loop_done : forall vs,
  absstep {| APc := Loop; AVars := vs |}
          {| APc := Done; AVars := vs |}
| AStep_Loop_enter : forall vs,
  absstep {| APc := Loop; AVars := vs |}
          {| APc := i_add_n; AVars := vs |}
| AStep_i_add_n_i_eq_j :
  absstep {| APc := i_add_n; AVars := i_eq_j |}
          {| APc := j_add_n; AVars := i_eq_j_plus_n |}
| AStep_i_add_n_Other : forall vs,
  vs <> i_eq_j
  -> absstep {| APc := i_add_n; AVars := vs |}
             {| APc := j_add_n; AVars := Unknown |}
| AStep_j_add_n_i_eq_j_plus_n :
  absstep {| APc := j_add_n; AVars := i_eq_j_plus_n |}
          {| APc := n_sub_1; AVars := i_eq_j |}
| AStep_j_add_n_i_Other : forall vs,
  vs <> i_eq_j_plus_n
  -> absstep {| APc := j_add_n; AVars := vs |}
             {| APc := n_sub_1; AVars := Unknown |}
| AStep_n_sub_1_bad :
  absstep {| APc := n_sub_1; AVars := i_eq_j_plus_n |}
          {| APc := Loop; AVars := Unknown |}
| AStep_n_sub_1_good : forall vs,
  vs <> i_eq_j_plus_n
  -> absstep {| APc := n_sub_1; AVars := vs |}
             {| APc := Loop; AVars := vs |}.

Definition absloopy_sys := {|
  Initial := { {| APc := i_gets_0; AVars := Unknown |} };
  Step := absstep
|}.

(* Now we need our simulation relation.  First, we define one just at the level
 * of local-variable state.  It formalizes our intuition about those values. *)
Inductive Rvars : vars -> absvars -> Prop :=
| Rv_Unknown : forall vs, Rvars vs Unknown
| Rv_i_is_0 : forall vs, vs.(I) = 0 -> Rvars vs i_is_0
| Rv_i_eq_j : forall vs, vs.(I) = vs.(J) -> Rvars vs i_eq_j
| Rv_i_eq_j_plus_n : forall vs, vs.(I) = vs.(J) + vs.(N) -> Rvars vs i_eq_j_plus_n.

(* We lift to full states in the obvious way. *)
Inductive R : state -> absstate -> Prop :=
| Rcon : forall pc vs avs, Rvars vs avs -> R {| Pc := pc; Vars := vs |}
                                             {| APc := pc; AVars := avs |}.

(* Now we are ready to prove the original system correct. *)
Theorem loopy_ok :
  invariantFor loopy_sys loopy_correct.
Proof.
  eapply invariant_weaken with (invariant1 := invariantViaSimulation R _).
  apply invariant_simulates with (sys2 := absloopy_sys).

  (* Here comes another boring simulation proof. *)
  constructor; simplify.

  invert H.
  exists {| APc := i_gets_0; AVars := Unknown |}.
  propositional.
  constructor.
  constructor.

  invert H0.

  invert H.
  exists {| APc := j_gets_0; AVars := i_is_0 |}.
  propositional; repeat constructor.

  invert H.
  invert H3.
  exists {| APc := Loop; AVars := Unknown |}; propositional; repeat constructor; equality.
  exists {| APc := Loop; AVars := i_eq_j |}; propositional; repeat constructor; equality.
  exists {| APc := Loop; AVars := Unknown |}; propositional; repeat constructor; equality.
  exists {| APc := Loop; AVars := Unknown |}; propositional; repeat constructor; equality.

  exists {| APc := Done; AVars := st2.(AVars) |}.
  invert H; simplify; propositional; repeat constructor; equality.

  exists {| APc := i_add_n; AVars := st2.(AVars) |}.
  invert H; simplify; propositional; repeat constructor; equality.

  invert H.
  invert H3.
  exists {| APc := j_add_n; AVars := Unknown |}; repeat constructor; equality.
  exists {| APc := j_add_n; AVars := Unknown |}; repeat constructor; equality.
  exists {| APc := j_add_n; AVars := i_eq_j_plus_n |}; repeat constructor; simplify; equality.
  exists {| APc := j_add_n; AVars := Unknown |}; repeat constructor; equality.

  invert H.
  invert H3.
  exists {| APc := n_sub_1; AVars := Unknown |}; repeat constructor; equality.
  exists {| APc := n_sub_1; AVars := Unknown |}; repeat constructor; equality.
  exists {| APc := n_sub_1; AVars := Unknown |}; repeat constructor; equality.
  exists {| APc := n_sub_1; AVars := i_eq_j |}; repeat constructor; simplify; equality.

  invert H.
  invert H3.
  exists {| APc := Loop; AVars := Unknown |}; propositional; repeat constructor; equality.
  exists {| APc := Loop; AVars := i_is_0 |}; propositional; repeat constructor; equality.
  exists {| APc := Loop; AVars := i_eq_j |}; propositional; repeat constructor; equality.
  exists {| APc := Loop; AVars := Unknown |}; propositional; repeat constructor; equality.

  (* Finally, we can call the model checker to find an invariant of the abstract
   * system. *)
  model_check_infer.
  (* We get 7 neat little states, one per program counter.  Next, we prove that
   * each of them implies the original invariant. *)

  invert 1.
  invert H0.
  unfold loopy_correct.
  simplify.
  propositional; subst.

  (* Most of the hypotheses we invert are contradictory, implying that distinct
   * program counters are equal. *)

  invert H2.

  invert H1.

  invert H2.

  invert H1.
  invert H.
  assumption.

  invert H2.

  invert H1.

  invert H2.
Qed.


(** * Modularity *)

(* Throughout the book, we'll come again and again to our two main weapons in
 * soundly modeling complex transition systems with simpler ones.  We just
 * learned about *abstraction*, to replace a full system with a simpler one.
 * The other key one is *modularity*, to replace a system with several others.
 * Let's study one example that helps with model checking, allowing us to check
 * programs with arbitrarily many threads running the same code, while still
 * finding an invariant automatically by brute-force enumeration. *)

(* The key to this particular technique is instrumenting a step relation to
 * consider *interference*, or the actions that other threads might take, in
 * between steps of the thread that we focus on.  This relation is parameterized
 * on an invariant [inv] that the other threads guarantee to preserve on the
 * shared state.  That is, the other threads may mess with the shared state
 * arbitrarily between our own steps, *but* they guarantee that every value they
 * set for it satisfies [inv]. *)
Inductive stepWithInterference shared private (inv : shared -> Prop)
          (step : threaded_state shared private -> threaded_state shared private -> Prop)
          : threaded_state shared private -> threaded_state shared private -> Prop :=

(* First kind of step: this thread runs in the normal way. *)
| StepSelf : forall st st',
  step st st'
  -> stepWithInterference inv step st st'

(* Second kind of step: other threads change shared state to some new value
 * satisfying [inv]. *)
| StepEnvironment : forall sh pr sh',
  inv sh'
  -> stepWithInterference inv step
                          {| Shared := sh; Private := pr |}
                          {| Shared := sh'; Private := pr |}.

(* Via this relation, we have an operator to build a new transition system from
 * an old one, given [inv]. *)
Definition withInterference shared private (inv : shared -> Prop)
           (sys : trsys (threaded_state shared private))
  : trsys (threaded_state shared private) := {|
  Initial := sys.(Initial);
  Step := stepWithInterference inv sys.(Step)
|}.

(* Tired of simulation proofs yet?  Then you'll love this theorem, which shows
 * a free simulation for any use of [withInterference]!  We even get to pick the
 * trivial simulation relation, state equality. *)
Theorem withInterference_abstracts : forall shared private (inv : shared -> Prop)
                                           (sys : trsys (threaded_state shared private)),
  simulates (fun st st' => st = st') sys (withInterference inv sys).
Proof.
  simplify.
  constructor; simplify.

  exists st1; propositional.

  exists st1'; propositional.
  constructor.
  equality.
Qed.

(* That proof was pretty straightforward, because we could construct the
 * simulation using only the first rule of [stepWithInterference], ignoring the
 * possibility for steps by other threads.  We go next for a theorem with an
 * intimidating statement and a much more interesting proof, whose details we
 * nonetheless won't comment on in text.  It may make sense to skip past the
 * next two lemma statements to the main theorem [withInterference_parallel]. *)
Lemma withInterference_parallel_init : forall shared private1 private2
                                          (invs : shared -> Prop)
                                          (sys1 : trsys (threaded_state shared private1))
                                          (sys2 : trsys (threaded_state shared private2))
                                          st st',
  (withInterference invs (parallel sys1 sys2)).(Step)^* st st'
  -> forall st1 st2,
      (forall st1', (withInterference invs sys1).(Step)^* st1 st1' -> invs st1'.(Shared))
      -> (forall st2', (withInterference invs sys2).(Step)^* st2 st2' -> invs st2'.(Shared))
      -> (withInterference invs sys1).(Step)^* st1
                                            {| Shared := st.(Shared);
                                               Private := fst st.(Private) |}
      -> (withInterference invs sys2).(Step)^* st2
                                            {| Shared := st.(Shared);
                                               Private := snd st.(Private) |}
      -> (withInterference invs sys1).(Step)^* st1
                                            {| Shared := st'.(Shared);
                                               Private := fst st'.(Private) |}.
Proof.
  induct 1; simplify.

  assumption.

  invert H; simplify.
  invert H5; simplify.

  apply IHtrc with (st2 := {| Shared := sh'; Private := pr2 |}).
  simplify.
  apply H1.
  assumption.
  simplify.
  eapply H2.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  apply StepEnvironment with (sh' := sh').
  apply H1 with (st1' := {| Shared := sh'; Private := pr1' |}).
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  econstructor.
  eassumption.
  constructor.
  assumption.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  econstructor.
  eassumption.
  constructor.
  constructor.

  apply IHtrc with (st2 := {| Shared := sh'; Private := pr2' |}).
  assumption.
  simplify.
  apply H2.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  constructor.
  eassumption.
  eassumption.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  apply StepEnvironment with (sh' := sh').
  apply H2 with (st2' := {| Shared := sh'; Private := pr2' |}).
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  econstructor.
  eassumption.
  constructor.
  constructor.
  constructor.

  apply IHtrc with (st2 := {| Shared := sh'; Private := snd pr |}).
  assumption.
  simplify.
  eapply H2.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  apply StepEnvironment with (sh' := sh').
  assumption.
  assumption.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  apply StepEnvironment with (sh' := sh').  
  assumption.
  constructor.
  constructor.
Qed.

Lemma withInterference_parallel_step : forall shared private1 private2
                                              (invs : shared -> Prop)
                                              (sys1 : trsys (threaded_state shared private1))
                                              (sys2 : trsys (threaded_state shared private2))
                                              st st',
  (withInterference invs (parallel sys1 sys2)).(Step)^* st st'
  -> forall st1 st2,
      (forall st1', (withInterference invs sys1).(Step)^* st1 st1' -> invs st1'.(Shared))
      -> (forall st2', (withInterference invs sys2).(Step)^* st2 st2' -> invs st2'.(Shared))
      -> (withInterference invs sys1).(Step)^* st1
                                            {| Shared := st.(Shared);
                                               Private := fst st.(Private) |}
      -> (withInterference invs sys2).(Step)^* st2
                                            {| Shared := st.(Shared);
                                               Private := snd st.(Private) |}
      -> (withInterference invs sys2).(Step)^* st2
                                            {| Shared := st'.(Shared);
                                               Private := snd st'.(Private) |}.
Proof.
  induct 1; simplify.

  assumption.

  invert H; simplify.
  invert H5; simplify.

  apply IHtrc with (st1 := {| Shared := sh'; Private := pr1' |}).
  simplify.
  apply H1.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  econstructor.
  eassumption.
  assumption.
  assumption.
  constructor.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  apply StepEnvironment with (sh' := sh').
  apply H1 with (st1' := {| Shared := sh'; Private := pr1' |}).
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  econstructor.
  eassumption.
  constructor.
  constructor.

  apply IHtrc with (st1 := {| Shared := sh'; Private := pr1 |}).
  simplify.
  apply H1.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  apply StepEnvironment with (sh' := sh').
  apply H2 with (st2' := {| Shared := sh'; Private := pr2' |}).
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  constructor.
  eassumption.
  constructor.
  assumption.
  assumption.
  constructor.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  constructor.
  eassumption.
  constructor.

  apply IHtrc with (st1 := {| Shared := sh'; Private := fst pr |}).
  simplify.
  eapply H1.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  apply StepEnvironment with (sh' := sh').
  assumption.
  assumption.
  assumption.
  constructor.
  eapply trc_trans.
  eassumption.
  eapply TrcFront.
  apply StepEnvironment with (sh' := sh').  
  assumption.
  constructor.
Qed.

(* OK, we made it to the main theorem.  It helps us find an invariant for a
 * [parallel] system to which we have applied the [withInterference]
 * construction.  Crucially, we may check the invariant for each constituent
 * thread *separately*, avoiding the combinatorial state-space explosion that
 * would come from analyzing the combined system directly.  This is the essence
 * of modularity! *)
Theorem withInterference_parallel : forall shared private1 private2
                                           (invs : shared -> Prop)
                                           (sys1 : trsys (threaded_state shared private1))
                                           (sys2 : trsys (threaded_state shared private2)),
    invariantFor (withInterference invs sys1)
                 (fun st => invs st.(Shared))
    -> invariantFor (withInterference invs sys2)
                    (fun st => invs st.(Shared))
    -> invariantFor (withInterference invs (parallel sys1 sys2))
                    (fun st => invs st.(Shared)).
Proof.
  unfold invariantFor.
  simplify.
  invert H1.

  (* [assert P]: first prove proposition [P], then continue with it as a new
   *   hypothesis. *)
  assert ((withInterference invs sys1).(Step)^*
             {| Shared := sh; Private := pr1 |}
             {| Shared := s'.(Shared); Private := fst s'.(Private) |}).
  apply withInterference_parallel_init with (sys2 := sys2)
                                            (st := {| Shared := sh; Private := (pr1, pr2) |})
                                            (st2 := {| Shared := sh; Private := pr2 |});
    simplify; propositional.
  apply H in H1; propositional.
  apply H0 in H1; propositional.
  constructor.
  constructor.

  assert ((withInterference invs sys2).(Step)^*
             {| Shared := sh; Private := pr2 |}
             {| Shared := s'.(Shared); Private := snd s'.(Private) |}).
  apply withInterference_parallel_step with (sys1 := sys1)
                                            (st := {| Shared := sh; Private := (pr1, pr2) |})
                                            (st1 := {| Shared := sh; Private := pr1 |});
    simplify; propositional.
  apply H in H5; propositional.
  apply H0 in H5; propositional.
  constructor.
  constructor.

  apply H in H1; try assumption.
Qed.

(* Let's apply this principle on a concrete example.  Consider a program with
 * many threads running calls to this function.
 * <<
    int global = 0;

    f() {
      int local = 0;

      while (true) {
        local = global;
        local = 3 + local;
        local = 7 + local;
        global = local;
      }
    }
   >>
 * Here's the usual formalization as a transition system. *)

Inductive twoadd_pc := ReadIt | Add3 | Add7 | WriteIt.

Definition twoadd_initial := { {| Shared := 0; Private := (ReadIt, 0) |} }.

Inductive twoadd_step : threaded_state nat (twoadd_pc * nat)
                        -> threaded_state nat (twoadd_pc * nat) -> Prop :=
| Step_ReadIt : forall g l,
  twoadd_step {| Shared := g; Private := (ReadIt, l) |}
              {| Shared := g; Private := (Add3, g) |}
| Step_Add3 : forall g l,
  twoadd_step {| Shared := g; Private := (Add3, l) |}
              {| Shared := g; Private := (Add7, 3 + l) |}
| Step_Add7 : forall g l,
  twoadd_step {| Shared := g; Private := (Add7, l) |}
              {| Shared := g; Private := (WriteIt, 7 + l) |}
| Step_WriteIt : forall g l,
  twoadd_step {| Shared := g; Private := (WriteIt, l) |}
              {| Shared := l; Private := (ReadIt, l) |}.

Definition twoadd_sys := {|
  Initial := twoadd_initial;
  Step := twoadd_step
|}.

(* Invariant to prove: the global variable is always even, again. *)
Definition twoadd_correct private (st : threaded_state nat private) :=
  isEven st.(Shared).

(* Here's an abstract version of the system where, much like before, we model
 * integers as Booleans, recording whether they are even or not. *)

Definition twoadd_ainitial := { {| Shared := true; Private := (ReadIt, true) |} }.

Inductive twoadd_astep : threaded_state bool (twoadd_pc * bool)
                        -> threaded_state bool (twoadd_pc * bool) -> Prop :=
| AStep_ReadIt : forall g l,
  twoadd_astep {| Shared := g; Private := (ReadIt, l) |}
               {| Shared := g; Private := (Add3, g) |}
| AStep_Add3 : forall g l,
  twoadd_astep {| Shared := g; Private := (Add3, l) |}
               {| Shared := g; Private := (Add7, negb l) |}
| AStep_Add7 : forall g l,
  twoadd_astep {| Shared := g; Private := (Add7, l) |}
               {| Shared := g; Private := (WriteIt, negb l) |}
| AStep_WriteIt : forall g l,
  twoadd_astep {| Shared := g; Private := (WriteIt, l) |}
               {| Shared := l; Private := (ReadIt, l) |}
| AStep_Someone_Made_It_Even : forall g pr,
  twoadd_astep {| Shared := g; Private := pr |}
               {| Shared := true; Private := pr |}.

Definition twoadd_asys := {|
  Initial := twoadd_ainitial;
  Step := twoadd_astep
|}.

(* Here's a simulation relation at the level of integers and their Boolean
 * counterparts. *)
Definition even_R (n : nat) (b : bool) :=
  isEven n <-> b = true.

(* A few unsurprising properties hold of [even_R]. *)

Lemma even_R_0 : even_R 0 true.
Proof.
  unfold even_R; propositional.
  constructor.
Qed.

Lemma even_R_forward : forall n, isEven n -> even_R n true.
Proof.
  unfold even_R; propositional.
Qed.

Lemma even_R_backward : forall n, even_R n true -> isEven n.
Proof.
  unfold even_R; propositional.
Qed.

Lemma even_R_add2 : forall n b,
  even_R n b
  -> even_R (S (S n)) b.
Proof.
  unfold even_R; propositional.
  invert H; propositional.
  constructor; assumption.
Qed.

(* The cases for evenness of an integer and its successor *)
Lemma isEven_decide : forall n,
  (isEven n /\ ~isEven (S n)) \/ (~isEven n /\ isEven (S n)).
Proof.
  induct n; simplify; propositional.

  left; propositional.
  constructor.
  invert H.

  right; propositional.
  constructor; assumption.

  left; propositional.
  invert H.
  propositional.
Qed.

Lemma even_R_add1 : forall n b,
  even_R n b
  -> even_R (S n) (negb b).
Proof.
  unfold even_R; simplify.
  assert ((isEven n /\ ~isEven (S n)) \/ (~isEven n /\ isEven (S n))).
  apply isEven_decide.
  cases b; simplify; propositional.
  equality.
  equality.
Qed.

(* Here's the top-level simulation relation for our choice of abstraction. *)
Inductive twoadd_R : threaded_state nat (twoadd_pc * nat)
                     -> threaded_state bool (twoadd_pc * bool) -> Prop :=
| Twoadd_R : forall pc gn ln gb lb,
  even_R gn gb
  -> even_R ln lb
  -> twoadd_R {| Shared := gn; Private := (pc, ln) |}
              {| Shared := gb; Private := (pc, lb) |}.

(* Step 1 of main proof: model-check an individual thread. *)
Lemma twoadd_ok :
  invariantFor (withInterference isEven twoadd_sys)
               (fun st => isEven (Shared st)).
Proof.
  eapply invariant_weaken.
  apply invariant_simulates with (sys2 := twoadd_asys) (R := twoadd_R).

  (* Boring simulation proof begins here. *)
  constructor; simplify.

  invert H.
  exists {| Shared := true; Private := (ReadIt, true) |}; propositional.
  constructor; propositional.
  apply even_R_0.
  apply even_R_0.
  constructor.
  equality.
  simplify.
  propositional.

  invert H0.
  invert H1.

  invert H.
  exists {| Shared := gb; Private := (Add3, gb) |}; propositional.
  constructor; propositional.
  constructor.

  invert H.
  exists {| Shared := gb; Private := (Add7, negb lb) |}; propositional.
  constructor; propositional.
  apply even_R_add2.
  apply even_R_add1.
  assumption.
  constructor.

  invert H.
  exists {| Shared := gb; Private := (WriteIt, negb lb) |}; propositional.
  constructor; propositional.
  repeat apply even_R_add2.
  apply even_R_add1.
  assumption.
  constructor.

  invert H.
  exists {| Shared := lb; Private := (ReadIt, lb) |}; propositional.
  constructor; propositional.
  constructor.

  invert H.
  exists {| Shared := true; Private := (pc0, lb) |}; propositional.
  constructor; propositional.
  apply even_R_forward.
  assumption.
  constructor.

  (* Now find an invariant automatically. *)
  model_check_infer.

  (* Now prove that the invariant implies the correctness condition. *)
  invert 1.
  invert H0.
  simplify.
  propositional.

  invert H0.
  apply even_R_backward.
  assumption.

  invert H1.
  apply even_R_backward.
  assumption.

  invert H0.
  apply even_R_backward.
  assumption.

  invert H1.
  apply even_R_backward.
  assumption.
Qed.

(* Step 2: lift that result to the two-thread system, with no new model
 * checking. *) 
Theorem twoadd2_ok :
  invariantFor (parallel twoadd_sys twoadd_sys) (twoadd_correct (private := _)).
Proof.
  eapply invariant_weaken.
  eapply invariant_simulates.
  apply withInterference_abstracts.
  apply withInterference_parallel.
  apply twoadd_ok.
  apply twoadd_ok.

  unfold twoadd_correct.
  invert 1.
  assumption.
Qed.

(* In fact, this modularity technique is so powerful that we now get correctness
 * for any number of threads, "for free"!  Here's a tactic definition, which we
 * won't explain, but which is able to derive correctness for any number of
 * threads, just by repeating use of [withInterference_parallel] and
 * [twoadd_ok]. *)
Ltac twoadd := eapply invariant_weaken; [ eapply invariant_simulates; [
                                          apply withInterference_abstracts
                                          | repeat (apply withInterference_parallel
                                                    || apply twoadd_ok) ]
                                        | unfold twoadd_correct; invert 1; assumption ].

(* For instance, let's verify the three-thread version. *)
Theorem twoadd3_ok :
  invariantFor (parallel twoadd_sys (parallel twoadd_sys twoadd_sys)) (twoadd_correct (private := _)).
Proof.
  twoadd.
Qed.

(* To save us time defining versions with many threads, here's a recursive
 * function, creating exponentially many threads with respect to its
 * parameter. *)
Fixpoint manyadds_state (n : nat) : Type :=
  match n with
  | O => twoadd_pc * nat
  | S n' => manyadds_state n' * manyadds_state n'
  end%type.

Fixpoint manyadds (n : nat) : trsys (threaded_state nat (manyadds_state n)) :=
  match n with
  | O => twoadd_sys
  | S n' => parallel (manyadds n') (manyadds n')
  end.

(* Here are some examples of the systems we produce. *)
Eval simpl in manyadds 0.
Eval simpl in manyadds 1.
Eval simpl in manyadds 2.
Eval simpl in manyadds 3.

Theorem twoadd4_ok :
  invariantFor (manyadds 4) (twoadd_correct (private := _)).
Proof.
  twoadd.
Qed.

Theorem twoadd6_ok :
  invariantFor (manyadds 6) (twoadd_correct (private := _)).
Proof.
  twoadd.
Qed.
