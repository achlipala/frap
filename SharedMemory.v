(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 17: Operational Semantics for Shared-Memory Concurrency
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Shared notations and definitions; main material starts afterward. *)

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
Definition heap := fmap nat nat.

Hint Extern 1 (_ <= _) => linear_arithmetic : core.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic : core.


(** * An object language with shared-memory concurrency *)

(* We're going to start investigating how to verify concurrent programs whose
 * behavior is given with operational semantics.  There are a variety of
 * different concurrency styles out there, with their distinctive practical and
 * theoretical benefits; we'll start with the most venerable style, shared
 * memory. *)

(* We'll build on the mixed-embedding languages from the last two chapter. 
 * Let's simplify the encoding by only working with commands that generate
 * [nat]. *)
Inductive cmd :=
| Return (r : nat)
| Bind (c1 : cmd) (c2 : nat -> cmd)
| Read (a : nat)
| Write (a v : nat)
| Fail

(* Now here's the new part: parallel composition of commands. *)
| Par (c1 c2 : cmd)

(* Let's also add locking commands, where locks are named by [nat]s. *)
| Lock (a : nat)
| Unlock (a : nat).

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Infix "||" := Par.

(* As the program runs, it has not just a heap but also a set of locks that are
 * taken at that moment. *)
Definition locks := set nat.

(* The first few rules below are basically the same as in last chapter, except
 * that we relax the restriction on only reading/writing addresses that are
 * explicitly mapped into the heap. *)
Inductive step : heap * locks * cmd -> heap * locks * cmd -> Prop :=
| StepBindRecur : forall c1 c1' c2 h h' l l',
  step (h, l, c1) (h', l', c1')
  -> step (h, l, Bind c1 c2) (h', l', Bind c1' c2)
| StepBindProceed : forall v c2 h l,
  step (h, l, Bind (Return v) c2) (h, l, c2 v)

| StepRead : forall h l a,
  step (h, l, Read a) (h, l, Return (h $! a))
| StepWrite : forall h l a v,
  step (h, l, Write a v) (h $+ (a, v), l, Return 0)

(* First interesting twist: we can "push steps through" the [Par] operator on
 * either side.  The choice of a side is the sole source of nondeterminism in
 * this semantics, corresponding to the whims of a scheduler. *)
| StepParRecur1 : forall h l c1 c2 h' l' c1',
  step (h, l, c1) (h', l', c1')
  -> step (h, l, Par c1 c2) (h', l', Par c1' c2)
| StepParRecur2 : forall h l c1 c2 h' l' c2',
  step (h, l, c2) (h', l', c2')
  -> step (h, l, Par c1 c2) (h', l', Par c1 c2')

(* To take a lock, it must not be held; and vice versa for releasing a lock. *)
| StepLock : forall h l a,
  ~a \in l
  -> step (h, l, Lock a) (h, {a} \cup l, Return 0)
| StepUnlock : forall h l a,
  a \in l
  -> step (h, l, Unlock a) (h, l \setminus {a}, Return 0).

Definition trsys_of (h : heap) (l : locks) (c : cmd) := {|
  Initial := {(h, l, c)};
  Step := step
|}.



(** * An example *)

(* In this lecture, we'll focus on model checking as our program-proof
 * technique.  Recall that model checking is all about reducing a problem to a
 * reachability question in a finite-state system.  Our programs here have the
 * (perhaps surprising!) property that termination is guaranteed, for any
 * initial state, regardless of how the scheduler behaves.  Therefore, all
 * programs of this language are finite-state and thus, in principle, amenable
 * to model checking!  (We were careful to leave out looping constructs.)
 * Let's define a simple two-thread program and model-check it. *)

(* Throughout this file, we'll only be verifying that no thread could ever reach
 * a [Fail] command that is next in line to execute, a property that is easy to
 * phrase as an invariant of the transition system.  Here's how to compute
 * whether a command is about to fail. *)
Fixpoint notAboutToFail (c : cmd) : bool :=
  match c with
  | Fail => false
  | Bind c1 _ => notAboutToFail c1
  | Par c1 c2 => notAboutToFail c1 && notAboutToFail c2
  | _ => true
  end.

Example two_increments_thread :=
  _ <- Lock 0;
  n <- Read 0;
  if n <=? 1 then
    _ <- Write 0 (n + 1);
    Unlock 0
  else
    Fail.

Example two_increments := two_increments_thread || two_increments_thread.

(* Next, we do one of our standard boring (and slow; sorry!) model-checking
 * proofs, where tactics explore the finite state space for us. *)
Theorem two_increments_ok :
  invariantFor (trsys_of $0 {} two_increments)
               (fun p => let '(_, _, c) := p in
                         notAboutToFail c = true).
Proof.
  unfold two_increments, two_increments_thread.
  simplify.
  eapply invariant_weaken.
  apply multiStepClosure_ok; simplify.

  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_done.

  simplify.
  propositional; subst; equality.
Qed.

(* Notice how every step of the process needs to consider all possibilities of
 * threads that could run next, which, in general, gives us state spaces of size
 * *exponential* in the program-text length.  That's really a shame from a
 * performance perspective, isn't it?  Our goal now will be to apply
 * *optimizations* that show equivalence with alternative transition systems
 * whose state spaces are smaller.  By the end, we'll be able to check
 * nontrivial concurrent programs by only computing state spaces with *linear*
 * size in program-text length!  (The catch is that the technique only applies
 * for programs accepted by a simple static analysis.) *)


(** * Optimization #1: always run all purely local actions first. *)

(* Here's a function that, in a single go, performs all simplifications that are
 * *thread-local*.  That is, no other thread can observe those steps, as they
 * don't touch the heap or lockset. *)
Fixpoint runLocal (c : cmd) : cmd :=
  match c with
  | Return _ => c
  | Bind c1 c2 =>
    match runLocal c1 with
    | Return v => runLocal (c2 v)
    | c1' => Bind c1' c2
    end
  | Read _ => c
  | Write _ _ => c
  | Fail => c
  | Par c1 c2 => Par (runLocal c1) (runLocal c2)
  | Lock _ => c
  | Unlock _ => c
  end.

(* We can define an alternative step relation that always runs [runLocal] as a
 * kind of postprocessing on the new command.  This way, the model checker won't
 * need to run separate exploration steps for all of those trivial
 * simplifications. *)
Inductive stepL : heap * locks * cmd -> heap * locks * cmd -> Prop :=
| StepL : forall h l c h' l' c',
  step (h, l, c) (h', l', c')
  -> stepL (h, l, c) (h', l', runLocal c').

Definition trsys_ofL (h : heap) (l : locks) (c : cmd) := {|
  Initial := {(h, l, runLocal c)};
  Step := stepL
|}.

(* Now we prove some basic facts; commentary resumes before [step_runLocal]. *)

Hint Constructors step stepL : core.

Lemma run_Return : forall h l r h' l' c,
  step^* (h, l, Return r) (h', l', c)
  -> h' = h /\ l' = l /\ c = Return r.
Proof.
  induct 1; eauto.
  invert H.
Qed.

Lemma run_Bind : forall h l c1 c2 h' l' c',
  step^* (h, l, Bind c1 c2) (h', l', c')
  -> (exists c1', step^* (h, l, c1) (h', l', c1')
                  /\ c' = Bind c1' c2)
     \/ (exists h'' l'' r, step^* (h, l, c1) (h'', l'', Return r)
                           /\ step^* (h'', l'', c2 r) (h', l', c')).
Proof.
  induct 1; eauto.
  invert H; eauto 10.

  Ltac inst H :=
    repeat match type of H with
           | _ = _ -> _ => specialize (H eq_refl)
           | forall x : ?T, _ =>
             let y := fresh in evar (y : T); let y' := eval unfold y in y in
               specialize (H y'); clear y
           end.

  inst IHtrc.
  first_order; eauto 10.
Qed.

Lemma StepBindRecur_star : forall c1 c1' c2 h h' l l',
    step^* (h, l, c1) (h', l', c1')
    -> step^* (h, l, Bind c1 c2) (h', l', Bind c1' c2).
Proof.
  induct 1; eauto.
  cases y.
  cases p.
  eauto.
Qed.

Lemma StepParRecur1_star : forall h l c1 c2 h' l' c1',
  step^* (h, l, c1) (h', l', c1')
  -> step^* (h, l, Par c1 c2) (h', l', Par c1' c2).
Proof.
  induct 1; eauto.
  cases y.
  cases p.
  eauto.
Qed.

Lemma StepParRecur2_star : forall h l c1 c2 h' l' c2',
  step^* (h, l, c2) (h', l', c2')
  -> step^* (h, l, Par c1 c2) (h', l', Par c1 c2').
Proof.
  induct 1; eauto.
  cases y.
  cases p.
  eauto.
Qed.

Hint Resolve StepBindRecur_star StepParRecur1_star StepParRecur2_star : core.

Lemma runLocal_idem : forall c, runLocal (runLocal c) = runLocal c.
Proof.
  induct c; simplify; eauto.
  cases (runLocal c); simplify; eauto.
  rewrite IHc; auto.
  rewrite IHc; auto.
  equality.
Qed.

(* The key correctness property: when an original step takes place, either it
 * has no effect or can be duplicated when we apply [runLocal] both *before* and
 * *after* the step. *)
Lemma step_runLocal : forall h l c h' l' c',
  step (h, l, c) (h', l', c')
  -> (runLocal c = runLocal c' /\ h = h' /\ l = l')
     \/ exists c'', step (h, l, runLocal c) (h', l', c'')
                    /\ runLocal c'' = runLocal c'.
Proof.
  induct 1; simplify; first_order; eauto.

  rewrite H0; equality.

  cases (runLocal c1).
  invert H0.
  rewrite <- H1; eauto.
  rewrite <- H1; eauto.
  rewrite <- H1; eauto.
  rewrite <- H1; eauto.
  rewrite <- H1; eauto.
  rewrite <- H1; eauto.
  rewrite <- H1; eauto.

  rewrite H0; equality.

  right; eexists; propositional.
  eauto.
  simplify.
  rewrite runLocal_idem; equality.
  equality.
  right; eexists; propositional.
  eauto.
  simplify.
  rewrite runLocal_idem; equality.
Qed.

(* That was the main punchline.  Commentary resumes at [step_stepL]. *)

Lemma step_stepL' : forall h l c h' l' c',
  step^* (h, l, c) (h', l', c')
  -> stepL^* (h, l, runLocal c) (h', l', runLocal c').
Proof.
  induct 1; simplify; eauto.
  cases y.
  cases p.
  inst IHtrc.
  apply step_runLocal in H; first_order; subst.
  rewrite H; eauto.
  econstructor.
  econstructor.
  eauto.
  equality.
Qed.

Theorem notAboutToFail_runLocal : forall c,
  notAboutToFail (runLocal c) = true
  -> notAboutToFail c = true.
Proof.
  induct c; simplify; auto.
  cases (runLocal c); simplify; auto.
  cases (runLocal c1); simplify; auto; propositional;
  repeat match goal with
         | [ H : _ |- _ ] => apply andb_true_iff in H; propositional
         | [ H : _ = _ |- _ ] => rewrite H
         end; try equality.
Qed.

(* The key proof principle: to verify a can-never-fail invariant for the
 * original semantics, it suffices to verify it for the new semantics
 * instead. *)
Theorem step_stepL : forall h l c ,
  invariantFor (trsys_ofL h l c) (fun p => let '(_, _, c) := p in
                                           notAboutToFail c = true)
  -> invariantFor (trsys_of h l c) (fun p =>
                                      let '(_, _, c) := p in
                                      notAboutToFail c = true).
Proof.
  unfold invariantFor; simplify.
  propositional; subst.

  cases s'.
  cases p.
  apply step_stepL' in H1.
  apply H in H1; eauto using notAboutToFail_runLocal.
Qed.

(* Now watch as we verify that last example in fewer steps, with a smaller
 * invariant! *)
Theorem two_increments_ok_again :
  invariantFor (trsys_of $0 {} two_increments)
               (fun p => let '(_, _, c) := p in
                         notAboutToFail c = true).
Proof.
  apply step_stepL.
  unfold two_increments, two_increments_thread.
  simplify.
  eapply invariant_weaken.
  apply multiStepClosure_ok; simplify.

  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_done.

  simplify.
  propositional; subst; equality.
Qed.


(** * Optimization #2: partial-order reduction *)

(* There was a key property lurking behind the soundness proof of our last
 * optimization: *commutativity*, one of the most common ways to tame the
 * state-space explosion from concurrency scheduling.  Specifically, the local
 * steps performed by [runLocal] all *commute* with any steps taken in other
 * threads, because they are agnostic to shared state.  Can we generalize the
 * technique to also harness commutativity of operations that *do* depend on the
 * shared state, but in particular controlled ways?  Why, yes we can!  The most
 * popular such technique from the model-checking world is
 * *partial-order reduction*. *)

(* First, here's an example where we should be able to do better than allowing
 * either thread to run in every step, as we model-check. *)
Example independent_threads :=
  (a <- Read 0;
   _ <- Write 1 (a + 1);
   a <- Read 1;
   if a ==n 1 then
     Return 0
   else
     Fail)
  || (b <- Read 2;
      Write 2 (b + 1)).

(* Unfortunately, our existing model-checker does in fact follow the
 * "exponential" strategy to build the state space. *)
Theorem independent_threads_ok :
  invariantFor (trsys_of $0 {} independent_threads)
               (fun p => let '(_, _, c) := p in
                         notAboutToFail c = true).
Proof.
  apply step_stepL.
  unfold independent_threads.
  simplify.
  eapply invariant_weaken.
  apply multiStepClosure_ok; simplify.

  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_done.

  simplify.
  propositional; subst; equality.
Qed.

(* It turns out that we can actually do model-checking where at each point we
 * only explore the result of running *the first thread that is ready*!  Such a
 * strategy isn't sound for all programs, but it is for our example here.  Why?
 * Every pair of atomic actions between threads *commutes*.  That is, neither
 * one affects whether the other is enabled to execute (the way that one [Lock]
 * can disable another), and running the two actions in either order modifies
 * shared state identically.  In such a case, we may always pick our favorite
 * thread to step next. *)

(* To make all that formal, we will do some static program analysis to summarize
 * which atomic actions a thread might take. *)
Record summary := {
  Reads : set nat;
  Writes : set nat;
  Locks : set nat
}.

(* Here is a relation to check the accuracy of a summary. *)
Inductive summarize : cmd -> summary -> Prop :=
| SumReturn : forall r s,
    summarize (Return r) s
| SumFail : forall s,
    summarize Fail s
| SumBind : forall c1 c2 s,
    summarize c1 s
    -> (forall r, summarize (c2 r) s)
       (* Note the approximation here: we consider all [r] values, even if some
        * are semantically impossible. *)
    -> summarize (Bind c1 c2) s
| SumRead : forall a s,
    a \in s.(Reads)
    -> summarize (Read a) s
| SumWrite : forall a v s,
    a \in s.(Writes)
    -> summarize (Write a v) s
| SumLock : forall a s,
    a \in s.(Locks)
    -> summarize (Lock a) s
| SumUnlock : forall a s,
    a \in s.(Locks)
    -> summarize (Unlock a) s
| SumPar : forall c1 c2 s,
    summarize c1 s
    -> summarize c2 s
    -> summarize (Par c1 c2) s.

(* To check commutativity, it is helpful to know which atomic command a thread
 * could run next.  We skip coverage of parallel compositions to make things
 * simple. *)
Inductive nextAction : cmd -> cmd -> Prop :=
| NaReturn : forall r,
    nextAction (Return r) (Return r)
| NaFail :
    nextAction Fail Fail
| NaRead : forall a,
    nextAction (Read a) (Read a)
| NaWrite : forall a v,
    nextAction (Write a v) (Write a v)
| NaLock : forall l,
    nextAction (Lock l) (Lock l)
| NaUnlock : forall l,
    nextAction (Unlock l) (Unlock l)
| NaBind : forall c1 c2 c,
    nextAction c1 c
    -> nextAction (Bind c1 c2) c.

(* We can succinctly capture which summaries describe threads that will commute
 * with a particular atomic action.  The guarantee applies not just to the
 * thread's first action but also to all others that it might reach later in
 * execution. *)
Definition commutes (c : cmd) (s : summary) : Prop :=
  match c with
  | Return _ => True
  | Fail => True
  | Read a => ~a \in s.(Writes)
  | Write a _ => ~a \in s.(Reads) \cup s.(Writes)
  | Lock a => ~a \in s.(Locks)
  | Unlock a => ~a \in s.(Locks)
  | _ => False
  end.

(* Now the new semantics: *)
Inductive stepC (s : summary)  : heap * locks * cmd -> heap * locks * cmd -> Prop :=

(* It is always OK to let the first thread run. *)
| StepFirst : forall h l c1 h' l' c1' c2,
  step (h, l, c1) (h', l', c1')
  -> stepC s (h, l, c1 || c2) (h', l', c1' || c2)

(* However, you may only pick another thread to run if it would be unsound to
 * consider just the first thread.  The negation of the soundness condition is
 * expressed in the first premise below. *)
| StepAny : forall h l c2 h' l' c2' c1,
  (forall c0 h'' l'' c1'', nextAction c1 c0
                           (* The first thread [c] has some atomic action [c0]
                            * ready to run. *)
                           -> commutes c0 s
                           (* All other threads only contain actions that commute
                            * with [c0]. *)

                           -> step (h, l, c1) (h'', l'', c1'')
                           (* Finally, [c] is actually enabled to run, which
                            * might not be the case if [c0] is a locking
                            * command. *)

                           -> False)

  (* If we passed that check, then we can step a single thread as expected! *)
  -> step (h, l, c2) (h', l', c2')
  -> stepC s (h, l, c1 || c2) (h', l', c1 || c2').

(* Notice how this definition turns the partial-order-reduction optimization
 * "off and on" during state-space exploration.  We only restrict our attention
 * to the first thread so long as the soundness condition above is true. *)

Definition trsys_ofC (s : summary) (h : heap) (l : locks) (c : cmd) := {|
  Initial := {(h, l, c)};
  Step := stepC s
|}.


(* Now we come to quite a few fairly complex lemmas.
 * First, [commutes] really does allow other commands to swap order with the
 * atomic action in question. *)
Lemma commutes_sound' : forall h l c2 h' l' c2',
  step (h, l, c2) (h', l', c2')
  -> forall s c1 h'' l'' c1', step (h', l', c1) (h'', l'', c1')
  -> summarize c2 s
  -> commutes c1 s
  -> exists h1 l1, step (h, l, c1) (h1, l1, c1')
                   /\ step (h1, l1, c2) (h'', l'', c2').
Proof.
  induct 1; simplify; eauto.

  invert H1.
  eapply IHstep in H0; eauto; first_order.
  eauto.

  invert H0; invert H; simplify; propositional; eauto.
  do 2 eexists; propositional.
  eauto.
  assert (a <> a0) by sets.
  replace (h' $! a) with (h' $+ (a0, v) $! a) by (simplify; equality).
  eauto.

  invert H0; invert H; simplify; propositional; eauto.
  do 2 eexists; propositional.
  eauto.
  assert (a <> a0) by sets.
  replace (h $+ (a, v) $+ (a0, v0)) with (h $+ (a0, v0) $+ (a, v)) by maps_equal.
  eauto.

  invert H1.
  eapply IHstep in H0; clear IHstep; eauto.
  first_order.
  eauto 10.

  invert H1.
  eapply IHstep in H0; clear IHstep; eauto.
  first_order.
  eauto 10.

  invert H1; invert H0; simplify; propositional; eauto.
  do 2 eexists; propositional.
  constructor.
  sets.
  replace ({a0, a} \cup l) with ({a} \cup ({a0} \cup l)) by sets.
  constructor.
  sets.
  do 2 eexists; propositional.
  constructor.
  sets; propositional.
  replace ({a} \cup l \setminus {a0}) with ({a} \cup (l \setminus {a0})) by sets.
  constructor.
  sets.

  invert H1; invert H0; simplify; propositional; eauto.
  do 2 eexists; propositional.
  constructor.
  sets.
  replace ({a0} \cup (l \setminus {a})) with (({a0} \cup l) \setminus {a}) by sets.
  constructor.
  sets.
  do 2 eexists; propositional.
  constructor.
  sets; propositional.
  replace ((l \setminus {a}) \setminus {a0}) with ((l \setminus {a0}) \setminus {a}) by sets.
  constructor.
  sets.
Qed.

(* Commentary now resumes at [commutes_sound]. *)

Lemma step_nextAction_Return : forall r h l c h' l' c',
    step (h, l, c) (h', l', c')
    -> nextAction c (Return r)
    -> h' = h /\ l' = l /\ (forall h'' l'', step (h'', l'', c) (h'', l'', c')).
Proof.
  induct 1; invert 1; propositional; eauto.
Qed.

Lemma step_nextAction_other : forall c0 h l c h' l' c',
    step (h, l, c) (h', l', c')
    -> nextAction c c0
    -> (forall r, c0 <> Return r)
    -> exists f c0', step (h, l, c0) (h', l', c0')
                     /\ c = f c0
                     /\ c' = f c0'
                     /\ forall h1 l1 h2 l2 c0'', step (h1, l1, c0) (h2, l2, c0'')
                                                 -> step (h1, l1, f c0) (h2, l2, f c0'').
Proof.
  induct 1; invert 1; first_order; subst; eauto.

  exists (fun X => x <- x X; c2 x); eauto 10.

  invert H3.
  unfold not in *; exfalso; eauto.

  exists (fun X => X); eauto.

  exists (fun X => X); eauto.

  exists (fun X => X); eauto 10.

  exists (fun X => X); eauto 10.
Qed.

Lemma nextAction_couldBe : forall c c0,
    nextAction c c0
    -> match c0 with
       | Return _ => True
       | Fail => True
       | Read _ => True
       | Write _ _ => True
       | Lock _ => True
       | Unlock _ => True
       | _ => False
       end.
Proof.
  induct 1; auto.
Qed.

(* [commutes] allows order-swapping even when the atomic action is embedded
 * further within the structure of a larger command. *)
Lemma commutes_sound : forall h l c2 h' l' c2',
  step (h, l, c2) (h', l', c2')
  -> forall s c1 c0 h'' l'' c1', step (h', l', c1) (h'', l'', c1')
  -> summarize c2 s
  -> nextAction c1 c0
  -> commutes c0 s
  -> exists h1 l1, step (h, l, c1) (h1, l1, c1')
                   /\ step (h1, l1, c2) (h'', l'', c2').
Proof.
  simplify.

  assert (Hc : commutes c0 s) by assumption.
  specialize (nextAction_couldBe H2).
  cases c0; propositional.

  assert (Hs : step (h', l', c1) (h'', l'', c1')) by assumption.
  eapply step_nextAction_Return in H0; eauto; propositional; subst.
  eauto.

  eapply step_nextAction_other in H0; eauto; first_order; subst; try equality.
  eapply commutes_sound' with (c2 := c2) (c1 := Read a) in H3; eauto.
  first_order; eauto.

  eapply step_nextAction_other in H0; eauto; first_order; subst; try equality.
  eapply commutes_sound' with (c2 := c2) (c1 := Write a v) in H; eauto; try solve [ simplify; sets ].
  first_order; eauto.

  eapply step_nextAction_other in H0; eauto; first_order; subst; try equality.
  invert H0.

  eapply step_nextAction_other in H0; eauto; first_order; subst; try equality.
  eapply commutes_sound' with (c2 := c2) (c1 := Lock a) in H3; eauto.
  first_order; eauto.

  eapply step_nextAction_other in H0; eauto; first_order; subst; try equality.
  eapply commutes_sound' with (c2 := c2) (c1 := Unlock a) in H3; eauto.
  first_order; eauto.
Qed.

Hint Constructors summarize : core.

(* The next two lemmas show that, once a summary is accurate for a command, it
 * remains accurate throughout the whole execution lifetime of the command. *)

Lemma summarize_step : forall h l c h' l' c' s,
  step (h, l, c) (h', l', c')
  -> summarize c s
  -> summarize c' s.
Proof.
  induct 1; invert 1; simplify; eauto.
Qed.

Lemma summarize_steps : forall h l c h' l' c' s,
  step^* (h, l, c) (h', l', c')
  -> summarize c s
  -> summarize c' s.
Proof.
  induct 1; eauto.
  cases y.
  cases p.
  eauto using summarize_step.
Qed.

(* The next technical device will require that we bound how many steps of
 * execution particular commands could run for.  We use a conservative
 * overapproximation that is easy to compute, phrased as a relation. *)

Inductive boundRunningTime : cmd -> nat -> Prop :=
| BrtReturn : forall r n,
    boundRunningTime (Return r) n
| BrtFail : forall n,
    boundRunningTime Fail n
| BrtRead : forall a n,
    boundRunningTime (Read a) (S n)
| BrtWrite : forall a v n,
    boundRunningTime (Write a v) (S n)
| BrtLock : forall a n,
    boundRunningTime (Lock a) (S n)
| BrtUnlock : forall a n,
    boundRunningTime (Unlock a) (S n)
| BrtBind : forall c1 c2 n1 n2,
    boundRunningTime c1 n1
    -> (forall r, boundRunningTime (c2 r) n2)
    -> boundRunningTime (Bind c1 c2) (S (n1 + n2))
| BrtPar : forall c1 c2 n1 n2,
    boundRunningTime c1 n1
    -> boundRunningTime c2 n2
    -> boundRunningTime (Par c1 c2) (S (n1 + n2)).
(* The extra [S] here may seem superfluous, but it helps make a certain
 * induction well-founded. *)

(* Perhaps surprisingly, there exist commands that have no finite time bounds!
 * Mixed-embedding languages often have these counterintuitive properties. *)
Fixpoint scribbly (n : nat) : cmd :=
  match n with
  | O => Return 0
  | S n' => _ <- Write n' 0; scribbly n'
  end.

Lemma scribbly_time : forall n m,
    boundRunningTime (scribbly n) m
    -> m >= n.
Proof.
  induct n; invert 1; auto.
  invert H2.
  specialize (H4 n0).
  apply IHn in H4.
  linear_arithmetic.
Qed.

Theorem boundRunningTime_not_total : exists c, forall n, ~boundRunningTime c n.
Proof.
  exists (n <- Read 0; scribbly n); propositional.
  invert H.
  specialize (H4 (S n2)).
  apply scribbly_time in H4.
  linear_arithmetic.
Qed.

Hint Constructors boundRunningTime : core.

(* Key property: taking a step of execution lowers the running-time bound. *)
Lemma boundRunningTime_step : forall c n h l h' l',
    boundRunningTime c n
    -> forall c', step (h, l, c) (h', l', c')
    -> exists n', boundRunningTime c' n' /\ n' < n.
Proof.
  induct 1; invert 1; simplify; eauto.

  apply IHboundRunningTime in H4; first_order; subst.
  eexists; propositional.
  eauto.
  linear_arithmetic.

  apply IHboundRunningTime1 in H3; first_order; subst.
  eauto 6.

  apply IHboundRunningTime2 in H3; first_order; subst.
  eauto 6.
Qed.

Lemma boundRunningTime_steps : forall h l c h' l' c',
    step^* (h, l, c) (h', l', c')
    -> forall n, boundRunningTime c n
    -> exists n', boundRunningTime c' n' /\ n' <= n.
Proof.
  induct 1; simplify; eauto.
  cases y.
  cases p.
  specialize (boundRunningTime_step H1 H); first_order.
  eapply IHtrc in H2; eauto.
  first_order.
  eauto.
Qed.

(* Here we get a bit naughty and begin to depend on *classical logic*, as with
 * the *law of the excluded middle*: [forall P, P \/ ~P].  You may not have
 * noticed that we've never applied that principle explicitly so far! *)

(* A very useful property: when a command has bounded running time, any
 * execution starting from that command can be *completed* to one ending in a
 * stuck state.  This property definitely wouldn't be true without the bound,
 * if our language had explicit, unbounded loops.
 *
 * The fun thing about this proof is that we are essentially using tactics to
 * define an interpreter for the object language, making arbitrary scheduling
 * choices.  Implicit in the derivation is a proof that this interpreter always
 * terminates, which we get by strong induction on the running-time bound. *)
Theorem complete_trace : forall k c n,
  boundRunningTime c n
  -> n <= k
  -> forall h l, exists h' l' c', step^* (h, l, c) (h', l', c')
                                  /\ (forall h'' l'' c'',
                                         step (h', l', c') (h'', l'', c'')
                                         -> False).
Proof.
  induct k; simplify.
  invert H; try linear_arithmetic.

  do 3 eexists; propositional.
  eauto.
  invert H.

  do 3 eexists; propositional.
  eauto.
  invert H.

  invert H.

  do 3 eexists; propositional.
  eauto.
  invert H.

  do 3 eexists; propositional.
  eauto.
  invert H.

  do 3 eexists; propositional.
  apply trc_one.
  eauto.
  invert H.

  do 3 eexists; propositional.
  apply trc_one.
  eauto.
  invert H.

  excluded_middle (a \in l).
  do 3 eexists; propositional.
  eauto.
  invert H1.
  sets.
  do 3 eexists; propositional.
  apply trc_one.
  eauto.
  invert H1.

  excluded_middle (a \in l).
  do 3 eexists; propositional.
  apply trc_one.
  eauto.
  invert H1.
  do 3 eexists; propositional.
  eauto.
  invert H1.
  sets.

  eapply IHk in H1; eauto; first_order.
  cases x1.
  specialize (H2 r).
  eapply IHk in H2; eauto; first_order.
  do 3 eexists; propositional.
  eapply trc_trans.
  apply StepBindRecur_star.
  eassumption.
  eapply TrcFront.
  eauto.
  eassumption.
  eauto.
  do 3 eexists; propositional.
  apply StepBindRecur_star.
  eassumption.
  invert H3.
  eauto.
  do 3 eexists; propositional.
  apply StepBindRecur_star.
  eassumption.
  invert H3.
  eauto.
  do 3 eexists; propositional.
  apply StepBindRecur_star.
  eassumption.
  invert H3.
  eauto.
  do 3 eexists; propositional.
  apply StepBindRecur_star.
  eassumption.
  invert H3.
  eauto.
  do 3 eexists; propositional.
  apply StepBindRecur_star.
  eassumption.
  invert H3.
  eauto.
  do 3 eexists; propositional.
  apply StepBindRecur_star.
  eassumption.
  invert H3.
  eauto.
  do 3 eexists; propositional.
  apply StepBindRecur_star.
  eassumption.
  invert H3.
  eauto.

  assert (Hb1 : boundRunningTime c1 n1) by assumption.
  assert (Hb2 : boundRunningTime c2 n2) by assumption.
  eapply IHk in H1; try linear_arithmetic; first_order.
  invert H.
  eapply IHk in H2; try linear_arithmetic; first_order.
  invert H.
  do 3 eexists; propositional.
  eauto.
  invert H; eauto.
  cases y.
  cases p.
  specialize (boundRunningTime_step Hb2 H3); first_order.
  assert (boundRunningTime (Par x1 c) (S (n1 + x3))) by eauto.
  eapply IHk in H6; try linear_arithmetic; first_order.
  do 3 eexists; propositional.
  eapply TrcFront.
  eauto.
  eassumption.
  eauto.
  cases y.
  cases p.
  specialize (boundRunningTime_step Hb1 H3); first_order.
  assert (boundRunningTime (Par c c2) (S (x2 + n2))) by eauto.
  eapply IHk in H6; try linear_arithmetic; first_order.
  do 3 eexists; propositional.
  eapply TrcFront.
  eauto.
  eassumption.
  eauto.
Qed.

(* We will apply completion to traces that end in violation of the
 * not-about-to-fail invariant.  It is important that any extension of such a
 * trace preserves that property. *)
Lemma notAboutToFail_step : forall h l c h' l' c',
    step (h, l, c) (h', l', c')
    -> notAboutToFail c = false
    -> notAboutToFail c' = false.
Proof.
  induct 1; simplify; eauto; try equality.

  apply andb_false_iff in H0.
  apply andb_false_iff.
  propositional.

  apply andb_false_iff in H0.
  apply andb_false_iff.
  propositional.
Qed.

Lemma notAboutToFail_steps : forall h l c h' l' c',
    step^* (h, l, c) (h', l', c')
    -> notAboutToFail c = false
    -> notAboutToFail c' = false.
Proof.
  induct 1; simplify; eauto.
  cases y.
  cases p.
  eauto using notAboutToFail_step.
Qed.

(* One last technical device: we define a variant of [step^*] that tracks how
 * many steps were made, which will come in handy for induction shortly. *)
Inductive stepsi : nat -> heap * locks * cmd -> heap * locks * cmd -> Prop :=
| StepsiO : forall st,
    stepsi O st st
| StepsiS : forall st1 st2 st3 i,
    step st1 st2
    -> stepsi i st2 st3
    -> stepsi (S i) st1 st3.

Hint Constructors stepsi : core.

Theorem steps_stepsi : forall st1 st2,
    step^* st1 st2
    -> exists i, stepsi i st1 st2.
Proof.
  induct 1; first_order; eauto.
Qed.

Hint Constructors stepC : core.

(* The next few lemmas are quite technical.  Commentary resumes for
 * [translate_trace]. *)

Lemma nextAction_det : forall c c0,
    nextAction c c0
    -> forall h l h' l' c', step (h, l, c) (h', l', c')
    -> forall h'' l'' c'', step (h, l, c) (h'', l'', c'')
    -> h' = h'' /\ l'' = l' /\ c'' = c'.
Proof.
  induct 1; invert 1; invert 1; auto.

  eapply IHnextAction in H2; eauto.
  equality.

  invert H2.

  invert H2.
Qed.

Lemma commute_writes : forall c1 c a s h l1' h' l' v,
  nextAction c1 c
  -> a \in Writes s
  -> commutes c s
  -> forall c1', step (h, l1', c1) (h', l', c1')
  -> step (h $+ (a, v), l1', c1) (h' $+ (a, v), l', c1').
Proof.
  induct 1; simplify.

  invert H1.

  invert H1.

  invert H1.
  replace (h' $! a0) with (h' $+ (a, v) $! a0).
  eauto.
  assert (a <> a0) by sets.
  simplify; equality.

  invert H1.
  replace (h $+ (a0, v0) $+ (a, v)) with (h $+ (a, v) $+ (a0, v0)).
  eauto.
  assert (a <> a0) by sets.
  maps_equal.

  invert H1.
  eauto.

  invert H1.
  eauto.

  invert H2; eauto.
Qed.

Lemma commute_locks : forall c1 c a s h l1' h' l',
  nextAction c1 c
  -> a \in Locks s
  -> commutes c s
  -> forall c1', step (h, l1', c1) (h', l', c1')
  -> step (h, {a} \cup l1', c1) (h', {a} \cup l', c1').
Proof.
  induct 1; simplify.

  invert H1.

  invert H1.

  invert H1; eauto.

  invert H1; eauto.

  invert H1.
  replace ({a} \cup ({l} \cup l1')) with ({l} \cup ({a} \cup l1')) by sets.
  constructor.
  sets.

  invert H1.
  replace ({a} \cup (l1' \setminus {l})) with (({a} \cup l1') \setminus {l}) by sets.
  constructor.
  sets.

  invert H2; eauto.
Qed.

Lemma commute_unlocks : forall c1 c a s h l1' h' l',
  nextAction c1 c
  -> a \in Locks s
  -> commutes c s
  -> forall c1', step (h, l1', c1) (h', l', c1')
  -> step (h, l1' \setminus {a}, c1) (h', l' \setminus {a}, c1').
Proof.
  induct 1; simplify.

  invert H1.

  invert H1.

  invert H1; eauto.

  invert H1; eauto.

  invert H1.
  replace (({l} \cup l1') \setminus {a}) with ({l} \cup (l1' \setminus {a})) by sets.
  constructor.
  sets.

  invert H1.
  replace ((l1' \setminus {l}) \setminus {a}) with ((l1' \setminus {a}) \setminus {l}) by sets.
  constructor.
  sets.

  invert H2; eauto.
Qed.

Lemma commutes_noblock : forall c c0,
  nextAction c c0
  -> forall h l h' l' c', step (h, l, c) (h', l', c')
  -> forall c1 s, summarize c1 s
  -> commutes c0 s
  -> forall h1' l1' c1', step (h, l, c1) (h1', l1', c1')
  -> exists h'' l'', step (h1', l1', c) (h'', l'', c').
Proof.
  induct 1; invert 1.

  induct 1; simplify; eauto.
  invert H0.
  invert H0.
  invert H3; eauto.
  invert H1; eauto.
  invert H1; eauto.
  assert (a0 <> a) by sets.
  replace (h' $! a) with (h' $+ (a0, v) $! a) by (simplify; equality).
  eauto.
  invert H1; eauto.
  invert H1; eauto.
  invert H2; eauto.

  induct 1; simplify; eauto.

  induct 1; simplify; eauto.
  invert H0.
  invert H0.
  invert H4; eauto.
  invert H2; eauto.
  invert H2; eauto.
  invert H2; eauto.
  do 2 eexists.
  constructor.
  sets.
  invert H2; eauto.
  do 2 eexists.
  constructor.
  sets.
  invert H3; eauto.

  induct 1; simplify; eauto.
  invert H0.
  invert H0.
  invert H4; eauto.
  invert H2; eauto.
  invert H2; eauto.
  invert H2; eauto.
  do 2 eexists.
  constructor.
  sets.
  invert H2; eauto.
  do 2 eexists.
  constructor.
  sets.
  invert H3; eauto.

  induct 1; simplify; eauto.
  invert H1.
  invert H1.
  invert H5; eauto.
  invert H3; eauto.
  invert H3.
  do 2 eexists; eapply commute_writes in H2; eauto.
  invert H3.
  do 2 eexists; eapply commute_locks in H2; eauto.
  invert H3.
  do 2 eexists; eapply commute_unlocks in H2; eauto.
  invert H1; eauto.

  eauto.
Qed.

Lemma translate_trace_commute : forall i h l c1 c2 h' l' c',
    stepsi (S i) (h, l, c1 || c2) (h', l', c')
    -> (forall h'' l'' c'', step (h', l', c') (h'', l'', c'') -> False)
    -> forall s, summarize c2 s
    -> forall x, nextAction c1 x
    -> commutes x s
    -> forall x0 x1 x2, step (h, l, c1) (x0, x1, x2)
    -> exists h'' l'', step (h, l, c1) (h'', l'', x2)
                       /\ stepsi i (h'', l'', x2 || c2) (h', l', c').
Proof.
  induct 1; simplify.
  invert H0.
  
  invert H.

  eapply nextAction_det in H5; try eapply H6; eauto; propositional; subst.
  eauto 10.

  eapply commutes_noblock in H3; eauto.
  first_order.
  exfalso; eauto.

  invert H.

  eapply nextAction_det in H5; try eapply H12; eauto; propositional; subst.
  eauto 10.

  assert (Hnext : nextAction c1 x) by assumption.
  eapply commutes_noblock in Hnext; eauto.
  first_order.
  eapply IHstepsi in H; clear IHstepsi; eauto using summarize_step.
  first_order.
  eapply commutes_sound with (c1 := c1) (c2 := c2) (c0 := x) in H; eauto.
  first_order.
  eauto 10.
Qed.

(* The heart of the soundness proof!  When a length-[i] derivation gets us to a
 * stuck state that is about to fail, and when we have summarized the program,
 * we can run that summary in the optimized semantics and also arrive at a state
 * that is about to fail.  Thus, if we explore the optimized state space and
 * find no failures, we can conclude lack of reachable failures in the original
 * state space. *)
Lemma translate_trace : forall i h l c1 c2 h' l' c',
    stepsi i (h, l, c1 || c2) (h', l', c')
    -> (forall h'' l'' c'', step (h', l', c') (h'', l'', c'') -> False)
    -> notAboutToFail c' = false
    -> forall s, summarize c2 s
    -> exists h' l' c'', (stepC s)^* (h, l, c1 || c2) (h', l', c'')
                         /\ notAboutToFail c'' = false.
Proof.
  induct i; simplify.

  invert H.
  eauto 10.

  excluded_middle (exists c0 h' l' c', nextAction c1 c0
                                       /\ commutes c0 s
                                       /\ step (h, l, c1) (h', l', c')).

  first_order.
  eapply translate_trace_commute in H; eauto.
  first_order.
  eapply IHi in H6; eauto.
  first_order.
  eauto 7.

  invert H.
  invert H5.

  eapply IHi in H6; eauto.
  first_order.
  eauto 7.

  eapply IHi in H6; eauto using summarize_step.
  first_order.
  do 3 eexists; propositional.
  2: apply H4.
  eauto 10.
Qed.

Require Import Classical.

(* This theorem brings it all together, to reduce one invariant-proof problem to
 * another that uses the optimized semantics. *)
Theorem step_stepC : forall h l c1 c2 s n,
  summarize c2 s
  -> boundRunningTime (c1 || c2) n
  -> invariantFor (trsys_ofC s h l (c1 || c2))
                  (fun p => let '(_, _, c) := p in
                            notAboutToFail c = true)
  -> invariantFor (trsys_of h l (c1 || c2))
                  (fun p =>
                     let '(_, _, c) := p in
                     notAboutToFail c = true).
Proof.
  simplify.
  apply NNPP; propositional.
  unfold invariantFor in H2.
  apply not_all_ex_not in H2; first_order.
  apply imply_to_and in H2; propositional.
  apply not_all_ex_not in H4; first_order.
  apply imply_to_and in H2; propositional.
  cases x0.
  cases p.
  subst.
  simplify.
  cases (notAboutToFail c); propositional.
  assert (exists n', boundRunningTime c n' /\ n' <= n) by eauto using boundRunningTime_steps.
  first_order.
  eapply complete_trace in H2; eauto.
  first_order.
  specialize (trc_trans H4 H2); simplify.
  assert (notAboutToFail x2 = false) by eauto using notAboutToFail_steps.
  unfold invariantFor in H1; simplify.
  apply steps_stepsi in H7; first_order.
  eapply translate_trace in H7; eauto.
  first_order.
  apply H1 in H7; auto.
  equality.
Qed.

(* Now we define some tactics to help us apply this technique automatically for
 * concrete programs.  As usual, we won't explain how the tactics work. *)

Ltac analyzer := repeat (match goal with
                         | [ |- context[if ?E then _ else _] ] => cases E
                         | _ => econstructor
                         end; simplify; try solve [ sets ]).

Ltac por_solve := simplify; repeat econstructor; sets; linear_arithmetic.

Ltac por_invert1 :=
  match goal with
  | [ H : forall (c0 : cmd) (h'' : heap) (l'' : locks) (c'' : cmd), _ -> _ |- _ ] =>
    (exfalso; eapply H; try por_solve; por_solve) || clear H
  | _ => model_check_invert1
  end.

Ltac por_invert := simplify; repeat por_invert1.

Ltac por_closure :=
  repeat (apply oneStepClosure_empty
          || (apply oneStepClosure_split; [ por_invert; try equality; solve [ singletoner ] | ])).

Ltac por_step := eapply MscStep; [ por_closure | simplify ].
Ltac por_done := apply MscDone.

(* OK, ready to return to our last example!  This time we will see state-space
 * exploration that steps a single thread at a time, where the final invariant
 * includes no states with multiple *partially executed* threads. *)
Theorem independent_threads_ok_again :
  invariantFor (trsys_of $0 {} independent_threads)
               (fun p => let '(_, _, c) := p in
                         notAboutToFail c = true).
Proof.
  (* We need to supply the summary when invoking the proof principle, though we
   * could also have used Ltac to compute it automatically. *)
  eapply step_stepC with (s := {| Reads := {2};
                                  Writes := {2};
                                  Locks := {} |}).
  analyzer.
  analyzer.

  eapply invariant_weaken.
  apply multiStepClosure_ok; simplify.

  por_step.
  por_step.
  por_step.
  por_step.
  por_step.
  por_step.
  por_step.
  por_step.
  por_step.
  por_step.
  por_done.

  sets.

  (* We computed an inexact running time.  By filling in zeroes for some
   * existential variables, we commit to a concrete bound. *)
  Grab Existential Variables.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
Qed.
