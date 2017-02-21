(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 14: Operational Semantics for Shared-Memory Concurrency
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Shared notations and definitions; main material starts afterward. *)

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
Definition heap := fmap nat nat.

Hint Extern 1 (_ <= _) => linear_arithmetic.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic.


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
  -> step (h, l, Lock a) (h, l \cup {a}, Return 0)
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

Hint Constructors step stepL.

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

Hint Resolve StepBindRecur_star StepParRecur1_star StepParRecur2_star.

Lemma runLocal_idem : forall c, runLocal (runLocal c) = runLocal c.
Proof.
  induct c; simplify; eauto.
  cases (runLocal c); simplify; eauto.
  rewrite IHc; auto.
  rewrite IHc; auto.
  equality.
Qed.

(* The key correctnss property: when an original step takes place, either it
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
 * *partial order reduction*. *)

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

(* To make all that formal, we will do some static program analyze to summarize
 * which atomic actions a thread might take. *)
Record summary := {
  Reads : set nat;
  Writes : set nat;
  Locks : set nat
}.

(* Here is a relation to check the accuracy of a summary for a single thread. *)
Inductive summarize : cmd -> summary -> Prop :=
| SumReturn : forall r s,
    summarize (Return r) s
| SumFail : forall s,
    summarize Fail s
| SumBind : forall c1 c2 s,
    summarize c1 s
    -> (forall r, summarize (c2 r) s)
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
    -> summarize (Unlock a) s.

(* And here's one to check the accuracy of a summary for a list of threads.
 * Each thread is packaged with its verified summary in the list. *)
Inductive summarizeThreads : cmd -> list (cmd * summary) -> Prop :=
| StPar : forall c1 c2 ss1 ss2,
    summarizeThreads c1 ss1
    -> summarizeThreads c2 ss2
    -> summarizeThreads (Par c1 c2) (ss1 ++ ss2)
| StAtomic : forall c s,
    summarize c s
    -> summarizeThreads c [(c, s)].
(* We will use these expanded lists as the command type in the new semantics. *)

(* To check commutativity, it is helpful to know which atomic command a thread
 * could run next. *)
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
Inductive stepC : heap * locks * list (cmd * summary) -> heap * locks * list (cmd * summary) -> Prop :=

(* It is always OK to let the first thread run. *)
| StepFirst : forall h l c h' l' c' s cs,
  step (h, l, c) (h', l', c')
  -> stepC (h, l, (c, s) :: cs) (h', l', (c', s) :: cs)

(* However, you may only pick another thread to run if it would be unsound to
 * consider just the first thread.  The negation of the soundness condition is
 * expressed in the first premise below. *)
| StepAny : forall h l c h' l' s cs1 c1 s1 cs2 c1',
  (forall c0 h'' l'' c'', nextAction c c0
                          (* The first thread [c] has some atomic action [c0]
                           * ready to run. *)
                          -> List.Forall (fun c_s => commutes c0 (snd c_s)) (cs1 ++ (c1, s1) :: cs2)
                          (* All other threads only contain actiosn that commute
                           * with [c0]. *)

                          -> step (h, l, c) (h'', l'', c'')
                          (* Finaly, [c] is actually enabled to run, which might
                           * not be the case if [c0] is a locking command. *)

                          -> False)

  (* If we passed that check, then we can step a single thread as expected! *)
  -> step (h, l, c1) (h', l', c1')
  -> stepC (h, l, (c, s) :: cs1 ++ (c1, s1) :: cs2) (h', l', (c, s) :: cs1 ++ (c1', s1) :: cs2).

(* Notice how this definition turns the partial-order-reduction optimization
 * "off and on" during state-space exploration.  We only restrict our attention
 * to the first thread so long as the soundness condition above is true. *)

Definition trsys_ofC (h : heap) (l : locks) (cs : list (cmd * summary)) := {|
  Initial := {(h, l, cs)};
  Step := stepC
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

  invert H1.

  invert H1; invert H0; simplify; propositional; eauto.
  do 2 eexists; propositional.
  constructor.
  sets.
  replace ((l \cup {a}) \cup {a0}) with ((l \cup {a0}) \cup {a}) by sets.
  constructor.
  sets.
  do 2 eexists; propositional.
  constructor.
  sets; propositional.
  replace (l \cup {a} \setminus {a0}) with ((l \setminus {a0}) \cup {a}) by sets.
  constructor.
  sets.

  invert H1; invert H0; simplify; propositional; eauto.
  do 2 eexists; propositional.
  constructor.
  sets.
  replace ((l \setminus {a}) \cup {a0}) with ((l \cup {a0}) \setminus {a}) by sets.
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

Hint Constructors summarize.

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
 * overapproximation that is easy to compute, phrased as a relation.
 * Yes, it is time to get scared, as we must define exponentiation to compute
 * large enough time bounds! *)
Fixpoint pow2 (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => pow2 n' * 2
  end.

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
    -> boundRunningTime (Par c1 c2) (pow2 (n1 + n2)).

(* Perhaps surprisingly, there exist commands that have no finite time bounds!
 * Mixed-embedding languages often have these counterintuitive properties. *)
Theorem boundRunningTime_not_total : exists c, forall n, ~boundRunningTime c n.
Proof.
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

  exists (n <- Read 0; scribbly n); propositional.
  invert H.
  specialize (H4 (S n2)).
  apply scribbly_time in H4.
  linear_arithmetic.
Qed.

(* Next, some boring properties of [pow2]. *)

Lemma pow2_pos : forall n,
    pow2 n > 0.
Proof.
  induct n; simplify; auto.
Qed.

Lemma pow2_mono : forall n m,
    n < m
    -> pow2 n < pow2 m.
Proof.
  induct 1; simplify; auto.
  specialize (pow2_pos n); linear_arithmetic.
Qed.

Hint Resolve pow2_mono.

Lemma pow2_incr : forall n,
    n < pow2 n.
Proof.
  induct n; simplify; auto.
Qed.

Hint Resolve pow2_incr.

Lemma pow2_inv : forall n m,
    pow2 n <= m
    -> n < m.
Proof.
  simplify.
  specialize (pow2_incr n).
  linear_arithmetic.
Qed.

Lemma use_pow2 : forall n m k,
    pow2 m <= S k
    -> n <= m
    -> n <= k.
Proof.
  simplify.
  apply pow2_inv in H.
  linear_arithmetic.
Qed.

Lemma use_pow2' : forall n m k,
    pow2 m <= S k
    -> n < m
    -> pow2 n <= k.
Proof.
  simplify.
  specialize (@pow2_mono n m).
  linear_arithmetic.
Qed.

Hint Constructors boundRunningTime.

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
Require Import Classical.

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
  specialize (pow2_pos (n1 + n2)).
  linear_arithmetic.

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

  destruct (classic (a \in l)).
  do 3 eexists; propositional.
  eauto.
  invert H1.
  sets.
  do 3 eexists; propositional.
  apply trc_one.
  eauto.
  invert H1.

  destruct (classic (a \in l)).
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
  eapply IHk in H1; eauto using use_pow2; first_order.
  invert H.
  eapply IHk in H2; eauto using use_pow2; first_order.
  invert H.
  do 3 eexists; propositional.
  eauto.
  invert H; eauto.
  cases y.
  cases p.
  specialize (boundRunningTime_step Hb2 H3); first_order.
  assert (boundRunningTime (Par x1 c) (pow2 (n1 + x3))) by eauto.
  eapply IHk in H6; eauto using use_pow2'; first_order.
  do 3 eexists; propositional.
  eapply TrcFront.
  eauto.
  eassumption.
  eauto.
  cases y.
  cases p.
  specialize (boundRunningTime_step Hb1 H3); first_order.
  assert (boundRunningTime (Par c c2) (pow2 (x2 + n2))) by eauto.
  eapply IHk in H6; eauto using use_pow2'; first_order.
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

Hint Constructors stepsi.

Theorem steps_stepsi : forall st1 st2,
    step^* st1 st2
    -> exists i, stepsi i st1 st2.
Proof.
  induct 1; first_order; eauto.
Qed.

(* Some helper lemmas about Coq's quantification over lists *)

Lemma Exists_app_fwd : forall A (P : A -> Prop) ls1 ls2,
    Exists P (ls1 ++ ls2)
    -> Exists P ls1 \/ Exists P ls2.
Proof.
  induct ls1; invert 1; simplify; subst; eauto.
  apply IHls1 in H1; propositional; eauto.
Qed.

Lemma Exists_app_bwd : forall A (P : A -> Prop) ls1 ls2,
    Exists P ls1 \/ Exists P ls2
    -> Exists P (ls1 ++ ls2).
Proof.
  induct ls1; simplify; propositional; eauto.
  invert H0.
  invert H0; eauto.
Qed.

Lemma Forall_app_fwd1 : forall A (P : A -> Prop) ls1 ls2,
    Forall P (ls1 ++ ls2)
    -> Forall P ls1.
Proof.
  induct ls1; invert 1; eauto.
Qed.

Lemma Forall_app_fwd2 : forall A (P : A -> Prop) ls1 ls2,
    Forall P (ls1 ++ ls2)
    -> Forall P ls2.
Proof.
  induct ls1; invert 1; simplify; subst; eauto.
Qed.

Hint Immediate Forall_app_fwd1 Forall_app_fwd2.

Lemma Forall_app_bwd : forall A (P : A -> Prop) ls1 ls2,
    Forall P ls1
    -> Forall P ls2
    -> Forall P (ls1 ++ ls2).
Proof.
  induct 1; simplify; eauto.
Qed.

Hint Resolve Forall_app_bwd.

Lemma Forall2 : forall A (P Q R : A -> Prop) ls,
    Forall P ls
    -> Forall Q ls
    -> (forall x, P x -> Q x -> R x)
    -> Forall R ls.
Proof.
  induct 1; invert 1; eauto.
Qed.

(* A connection between [notAboutToFail] in the old and new worlds *)
Lemma summarizeThreads_aboutToFail : forall c cs,
    summarizeThreads c cs
    -> notAboutToFail c = false
    -> Exists (fun c_s => notAboutToFail (fst c_s) = false) cs.
Proof.
  induct 1; simplify; eauto.

  apply andb_false_iff in H1; propositional; eauto using Exists_app_bwd.
Qed.

Hint Resolve summarizeThreads_aboutToFail.

Lemma summarizeThreads_nonempty : forall c,
    summarizeThreads c []
    -> False.
Proof.
  induct 1.
  cases ss1; simplify; eauto.
  equality.
Qed.

Hint Immediate summarizeThreads_nonempty.

Hint Constructors stepC summarizeThreads.

(* When we step a summarized thread, we can duplicate the step within one of the
 * elements of the summary. *)
Lemma step_pick : forall h l c h' l' c',
    step (h, l, c) (h', l', c')
    -> forall cs, summarizeThreads c cs
    -> exists cs1 c0 s cs2 c0', cs = cs1 ++ (c0, s) :: cs2
                                /\ step (h, l, c0) (h', l', c0')
                                /\ summarizeThreads c' (cs1 ++ (c0', s) :: cs2).
Proof.
  induct 1; invert 1.

  eexists [], _, _, [], _; simplify; propositional; eauto 10 using summarize_step.

  eexists [], _, _, [], _; simplify; propositional; eauto 10 using summarize_step.

  eexists [], _, _, [], _; simplify; propositional; eauto 10 using summarize_step.

  eexists [], _, _, [], _; simplify; propositional; eauto 10 using summarize_step.

  apply IHstep in H3; first_order; subst.
  rewrite <- app_assoc.
  simplify.
  do 5 eexists; propositional.
  eauto.
  change (x ++ (x3, x1) :: x2 ++ ss2)
         with (x ++ ((x3, x1) :: x2) ++ ss2).
  rewrite app_assoc.
  eauto.

  invert H1.

  apply IHstep in H5; first_order; subst.
  rewrite app_assoc.
  do 5 eexists; propositional.
  eauto.
  rewrite <- app_assoc.
  eauto.

  invert H1.

  eexists [], _, _, [], _; simplify; propositional; eauto using summarize_step.

  eexists [], _, _, [], _; simplify; propositional; eauto using summarize_step.

  (* Here's a gnarly bit to make up for simplification in the proof above.
   * Some existential variables weren't determined, but we can pick their values
   * here. *)
  Grab Existential Variables.
  exact l'.
  exact h'.
Qed.

(* The next few lemmas are quite technical.  Commentary resumes for
 * [translate_trace]. *)

Lemma translate_trace_matching : forall h l c h' l' c',
    step (h, l, c) (h', l', c')
    -> forall c0 s cs, summarizeThreads c ((c0, s) :: cs)
    -> ~(exists c1 h'0 l'0 c'0,
            nextAction c0 c1
            /\ Forall (fun c_s => commutes c1 (snd c_s)) cs
            /\ step (h, l, c0) (h'0, l'0, c'0))
    -> exists cs', stepC (h, l, (c0, s) :: cs) (h', l', cs')
                   /\ summarizeThreads c' cs'.
Proof.
  simplify.
  eapply step_pick in H; eauto.
  first_order; subst.

  cases x; simplify.

  invert H.
  eauto.

  invert H.
  eauto 10.
Qed.

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

Lemma split_center : forall A (x : A) l1 l2 r1 r2,
    l1 ++ l2 = r1 ++ x :: r2
    -> (exists r21, r2 = r21 ++ l2
                    /\ l1 = r1 ++ x :: r21)
       \/ (exists r12, r1 = l1 ++ r12
                       /\ l2 = r12 ++ x :: r2).
Proof.
  induct l1; simplify; subst; eauto.

  cases r1; simplify.
  invert H; eauto.
  invert H.
  apply IHl1 in H2; first_order; subst; eauto.
Qed.

Hint Rewrite app_length.

Lemma step_into_summarizeThreads : forall c0 cs1 c s cs2,
    summarizeThreads c0 (cs1 ++ (c, s) :: cs2)
    -> forall h l h' l' c', step (h, l, c) (h', l', c')
    -> exists c0', step (h, l, c0) (h', l', c0')
                   /\ summarizeThreads c0' (cs1 ++ (c', s) :: cs2).
Proof.
  induct 1; simplify.
  apply split_center in x; first_order; subst.
  
  eapply IHsummarizeThreads1 in H1; eauto.
  first_order.
  eexists; propositional.
  eauto.
  change (summarizeThreads (x0 || c2) (cs1 ++ ((c', s) :: x) ++ ss2)).
  rewrite app_assoc.
  eauto.

  eapply IHsummarizeThreads2 in H1; eauto.
  first_order.
  rewrite <- app_assoc.
  eauto.

  cases cs1; simplify.
  invert x.
  eauto using summarize_step.

  invert x.
  apply (f_equal (@length _)) in H3; simplify.
  linear_arithmetic.
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
  -> step (h, l1' \cup {a}, c1) (h', l' \cup {a}, c1').
Proof.
  induct 1; simplify.

  invert H1.

  invert H1.

  invert H1; eauto.

  invert H1; eauto.

  invert H1.
  replace ((l1' \cup {l}) \cup {a}) with ((l1' \cup {a}) \cup {l}) by sets.
  constructor.
  sets.

  invert H1.
  replace ((l1' \setminus {l}) \cup {a}) with ((l1' \cup {a}) \setminus {l}) by sets.
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
  replace (l1' \cup {l} \setminus {a}) with ((l1' \setminus {a}) \cup {l}) by sets.
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

  eauto.
Qed.

Lemma split_app : forall A (l1 l2 r1 r2 : list A),
    l1 ++ l2 = r1 ++ r2
    -> (exists r12, r1 = l1 ++ r12
                    /\ l2 = r12 ++ r2)
       \/ (exists r21, r2 = r21 ++ l2
                       /\ l1 = r1 ++ r21).
Proof.
  induct l1; simplify; subst; eauto.

  cases r1; simplify; subst.
  right; eexists (_ :: _); simplify; eauto.
  invert H.
  first_order; subst; eauto.
  apply IHl1 in H2; first_order; subst; eauto.
Qed.

Hint Rewrite app_length.

Lemma step_out_of_summarizeThreads : forall c cs1 c0 s cs2,
    summarizeThreads c (cs1 ++ (c0, s) :: cs2)
    -> forall h l c0' s' h' l', step (h, l, c0') (h', l', c0)
    -> summarize c0' s'
    -> exists c', summarizeThreads c' (cs1 ++ (c0', s') :: cs2)
                  /\ step (h, l, c') (h', l', c).
Proof.
  induct 1; simplify.

  apply split_center in x; first_order; subst.
  
  eapply IHsummarizeThreads1 in H1; try reflexivity; eauto.
  first_order.
  change (cs1 ++ (c0', s') :: x ++ ss2) with (cs1 ++ ((c0', s') :: x) ++ ss2).
  rewrite app_assoc.
  eauto.

  eapply IHsummarizeThreads2 in H1; try reflexivity; eauto.
  first_order.
  rewrite <- app_assoc.
  eauto.

  cases cs1; simplify.
  invert x.
  eauto using summarize_step.
  invert x.
  cases cs1; simplify; try equality.
Qed.

Lemma translate_trace_commute : forall i h l c h' l' c',
    stepsi (S i) (h, l, c) (h', l', c')
    -> (forall h'' l'' c'', step (h', l', c') (h'', l'', c'') -> False)
    -> forall c0 s cs, summarizeThreads c ((c0, s) :: cs)
    -> forall x, nextAction c0 x
    -> Forall (fun c_s => summarize (fst c_s) (snd c_s) /\ commutes x (snd c_s)) cs
    -> forall x0 x1 x2, step (h, l, c0) (x0, x1, x2)
    -> exists h'' l'' c'', step (h, l, c0) (h'', l'', x2)
                           /\ summarizeThreads c'' ((x2, s) :: cs)
                           /\ stepsi i (h'', l'', c'') (h', l', c').
Proof.
  induct 1; simplify.
  invert H0.

  clear IHstepsi.
  eapply step_pick in H; eauto.
  first_order; subst.

  cases x3; simplify.
  invert H.
  eapply nextAction_det in H0; try eapply H5; eauto; propositional; subst.
  eauto 10.

  invert H.
  change ((c0, s) :: x3 ++ (x4, x5) :: x6)
  with (((c0, s) :: x3) ++ (x4, x5) :: x6) in H2.
  eapply step_into_summarizeThreads in H2; eauto.
  first_order.
  apply Forall_app_fwd2 in H4.
  invert H4; simplify; propositional.
  eapply commutes_noblock in H3; eauto.
  first_order.
  eapply step_into_summarizeThreads with (cs1 := []) in H6; eauto.
  first_order.

  cases st2.
  cases p.
  cases st0.
  cases p.
  eapply step_pick in H; eauto.
  first_order.

  cases x3; simplify.
  invert H.
  eapply nextAction_det in H0; try eapply H5; eauto; propositional; subst.
  eauto 10.

  invert H.
  change ((c0, s) :: x3 ++ (x4, x5) :: x6)
  with (((c0, s) :: x3) ++ (x4, x5) :: x6) in H2.
  eapply step_into_summarizeThreads in H2; eauto.
  first_order.
  specialize (Forall_app_fwd1 _ _ H4).
  apply Forall_app_fwd2 in H4.
  invert H4; simplify; propositional.
  assert (Hn : nextAction c0 x) by assumption.
  eapply commutes_noblock in H3; eauto.
  first_order.
  eapply IHstepsi in H3; clear IHstepsi; eauto using summarize_step.
  first_order.
  eapply commutes_sound with (c1 := c0) (c2 := x4) (c0 := x) in H10; eauto.
  first_order.
  eapply step_out_of_summarizeThreads with (cs1 := (x2, s) :: x3) in H11; eauto.
  simplify; first_order.
  eauto 10.
Qed.

Lemma summarizeThreads_Forall : forall c cs,
    summarizeThreads c cs
    -> Forall (fun c_s => summarize (fst c_s) (snd c_s)) cs.
Proof.
  induct 1; eauto.
Qed.

(* The heart of the soundness proof!  When a length-[i] derivation gets us to a
 * stuck state that is about to fail, and when we have summarized the program,
 * we can run that summary in the optimized semantics and also arrive at a state
 * that is about to fail.  Thus, if we explore the optimized state space and
 * find no failures, we can conclude lack of reachable failures in the original
 * state space. *)
Lemma translate_trace : forall i h l c h' l' c',
    stepsi i (h, l, c) (h', l', c')
    -> (forall h'' l'' c'', step (h', l', c') (h'', l'', c'') -> False)
    -> notAboutToFail c' = false
    -> forall cs, summarizeThreads c cs
    -> exists h' l' cs', stepC^* (h, l, cs) (h', l', cs')
                         /\ Exists (fun c_s => notAboutToFail (fst c_s) = false) cs'.
Proof.
  induct i; simplify.

  invert H.
  eauto 10.

  cases cs.
  exfalso; eauto.
  cases p.
  destruct (classic (exists c1 h' l' c', nextAction c0 c1
                                         /\ Forall (fun c_s => commutes c1 (snd c_s)) cs
                                         /\ step (h, l, c0) (h', l', c'))).

  first_order.
  eapply translate_trace_commute in H; eauto.
  first_order.
  eapply IHi in H7; eauto.
  first_order.
  do 3 eexists; propositional.
  eapply TrcFront.
  eauto.
  eassumption.
  assumption.
  apply summarizeThreads_Forall in H2.
  invert H2.
  eauto using Forall2.

  invert H.  
  cases st2.
  cases p.
  eapply translate_trace_matching in H5; eauto.
  first_order.
  eapply IHi in H6; eauto.
  first_order.
  eauto 6.
Qed.

Lemma Forall_Exists_contra : forall A (f : A -> bool) ls,
    Exists (fun x => f x = false) ls
    -> Forall (fun x => f x = true) ls
    -> False.
Proof.
  induct 1; invert 1; equality.
Qed.

(* This theorem brings it all together, to reduce one invariant-proof problem to
 * another that uses the optimized semantics. *)
Theorem step_stepC : forall h l c (cs : list (cmd * summary)) n,
  summarizeThreads c cs
  -> boundRunningTime c n
  -> invariantFor (trsys_ofC h l cs) (fun p => let '(_, _, cs) := p in
                                               List.Forall (fun c_s => notAboutToFail (fst c_s) = true) cs)
  -> invariantFor (trsys_of h l c) (fun p =>
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
  cases (notAboutToFail c0); propositional.
  assert (exists n', boundRunningTime c0 n' /\ n' <= n) by eauto using boundRunningTime_steps.
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
  eapply Forall_Exists_contra.
  apply H9.
  assumption.
Qed.

(* Now we define some tactics to help us apply this technique automatically for
 * concrete programs.  As usual, we won't explain how the tactics work. *)

Ltac analyzer := repeat (match goal with
                         | [ |- context[if ?E then _ else _] ] => cases E
                         | _ => econstructor
                         end; simplify; try solve [ sets ]).

Ltac por_solve := simplify; repeat econstructor; sets; linear_arithmetic.

Ltac por_lister :=
  repeat match goal with
         | [ H : ?ls ++ _ = _ :: _ |- _ ] => cases ls; simplify; invert H
         | [ H : @eq (list _) _ _ |- _ ] => apply (f_equal (@length _)) in H; simplify; linear_arithmetic
         end.

Ltac por_invert1 :=
  match goal with
  | [ H : forall (c0 : cmd) (h'' : heap) (l'' : locks) (c'' : cmd), _ -> _ |- _ ] =>
    (exfalso; eapply H; try por_solve; por_lister; por_solve) || (clear H; por_lister)
  | _ => model_check_invert1
  end.

Ltac por_invert := simplify; repeat por_invert1.

Ltac por_closure :=
  repeat (apply oneStepClosure_empty
          || (apply oneStepClosure_split; [ por_invert; try equality; solve [ singletoner ] | ])).

Ltac por_step :=
  eapply MscStep; [ por_closure | simplify ].

Ltac por_done :=
  apply MscDone; eapply oneStepClosure_solve; [ por_closure | simplify; solve [ sets ] ].

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
  eapply step_stepC with (cs := [(_, {| Reads := {0, 1};
                                        Writes := {1};
                                        Locks := {} |})]
                                  ++ [(_, {| Reads := {2};
                                             Writes := {2};
                                             Locks := {} |})]).
  analyzer.
  analyzer.

  simplify.
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
