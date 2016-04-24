(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 13: Operational Semantics for Shared-Memory Concurrency
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Shared notations and definitions; main material starts afterward. *)

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
Definition heap := fmap nat nat.
Definition assertion := heap -> Prop.

Hint Extern 1 (_ <= _) => linear_arithmetic.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic.

Ltac simp := repeat (simplify; subst; propositional;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         end); try linear_arithmetic.


(** * An object language with shared-memory concurrency *)

(* Let's simplify the encoding by only working with commands that generate
 * [nat]. *)
Inductive loop_outcome :=
| Done (a : nat)
| Again (a : nat).

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

Definition locks := set nat.

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

| StepParRecur1 : forall h l c1 c2 h' l' c1',
  step (h, l, c1) (h', l', c1')
  -> step (h, l, Par c1 c2) (h', l', Par c1' c2)
| StepParRecur2 : forall h l c1 c2 h' l' c2',
  step (h, l, c2) (h', l', c2')
  -> step (h, l, Par c1 c2) (h', l', Par c1 c2')
| StepParProceed : forall h l r c,
   step (h, l, Par (Return r) c) (h, l, c)

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


Example two_increments_thread :=
  _ <- Lock 0;
  n <- Read 0;
  _ <- Write 0 (n + 1);
  Unlock 0.

Example two_increments :=
  _ <- (two_increments_thread || two_increments_thread);
  n <- Read 0;
  if n ==n 2 then
    Return 0
  else
    Fail.

Fixpoint notAboutToFail (c : cmd) : bool :=
  match c with
  | Fail => false
  | Bind c1 _ => notAboutToFail c1
  | Par c1 c2 => notAboutToFail c1 && notAboutToFail c2
  | _ => true
  end.

Theorem two_increments_ok :
  invariantFor (trsys_of $0 {} two_increments)
               (fun p => let '(_, _, c) := p in
                         notAboutToFail c = true).
Proof.
Admitted.
(*  unfold two_increments, two_increments_thread.
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
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_done.

  simplify.
  propositional; subst; equality.
Qed.*)


(** * Optimization #1: always run all purely local actions first. *)

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
  | Par c1 c2 =>
    match runLocal c1 with
    | Return _ => runLocal c2
    | c1' => Par c1' (runLocal c2)
    end
  | Lock _ => c
  | Unlock _ => c
  end.

Inductive stepL : heap * locks * cmd -> heap * locks * cmd -> Prop :=
| StepL : forall h l c h' l' c',
  step (h, l, c) (h', l', c')
  -> stepL (h, l, c) (h', l', runLocal c').

Definition trsys_ofL (h : heap) (l : locks) (c : cmd) := {|
  Initial := {(h, l, runLocal c)};
  Step := stepL
|}.

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
  cases (runLocal c1); simplify; eauto.
  rewrite IHc1; equality.
  rewrite IHc2; equality.
  rewrite IHc2; equality.
  rewrite IHc2; equality.
  rewrite IHc1; equality.
  rewrite IHc2; equality.
  rewrite IHc2; equality.
Qed.

Lemma runLocal_left : forall c1 c2,
  (forall r, runLocal c1 <> Return r)
  -> runLocal (c1 || c2) = runLocal c1 || runLocal c2.
Proof.
  simplify.
  cases (runLocal c1); eauto.
  unfold not in *.
  exfalso; eauto.
Qed.

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

  cases (runLocal c1).
  invert H0.
  rewrite <- H1.
  right.
  eexists.
  propositional.
  eauto.
  simplify.
  rewrite runLocal_idem.
  equality.
  rewrite <- H1.
  right.
  eexists.
  propositional.
  eauto.
  simplify.
  rewrite runLocal_idem.
  equality.
  rewrite <- H1.
  right.
  eexists.
  propositional.
  eauto.
  simplify.
  rewrite runLocal_idem.
  equality.
  rewrite <- H1.
  right.
  eexists.
  propositional.
  eauto.
  simplify.
  rewrite runLocal_idem.
  equality.
  rewrite <- H1.
  right.
  eexists.
  propositional.
  eauto.
  simplify.
  rewrite runLocal_idem.
  equality.
  rewrite <- H1.
  right.
  eexists.
  propositional.
  eauto.
  simplify.
  rewrite runLocal_idem.
  equality.
  rewrite <- H1.
  right.
  eexists.
  propositional.
  eauto.
  simplify.
  rewrite runLocal_idem.
  equality.

  rewrite H0; equality.

  right.
  cases (runLocal c1); eauto.
  eexists; propositional.
  eauto.
  rewrite runLocal_left.
  rewrite <- Heq.
  rewrite runLocal_idem.
  equality.
  rewrite <- Heq.
  rewrite runLocal_idem.
  rewrite Heq.
  equality.

  eexists; propositional.
  eauto.
  rewrite runLocal_left.
  rewrite <- Heq.
  rewrite runLocal_idem.
  equality.
  rewrite <- Heq.
  rewrite runLocal_idem.
  rewrite Heq.
  equality.

  eexists; propositional.
  eauto.
  rewrite runLocal_left.
  rewrite <- Heq.
  rewrite runLocal_idem.
  equality.
  rewrite <- Heq.
  rewrite runLocal_idem.
  rewrite Heq.
  equality.

  eexists; propositional.
  eauto.
  rewrite runLocal_left.
  rewrite <- Heq.
  rewrite runLocal_idem.
  equality.
  rewrite <- Heq.
  rewrite runLocal_idem.
  rewrite Heq.
  equality.

  eexists; propositional.
  eauto.
  rewrite runLocal_left.
  rewrite <- Heq.
  rewrite runLocal_idem.
  equality.
  rewrite <- Heq.
  rewrite runLocal_idem.
  rewrite Heq.
  equality.

  eexists; propositional.
  eauto.
  rewrite runLocal_left.
  rewrite <- Heq.
  rewrite runLocal_idem.
  equality.
  rewrite <- Heq.
  rewrite runLocal_idem.
  rewrite Heq.
  equality.

  eexists; propositional.
  eauto.
  rewrite runLocal_left.
  rewrite <- Heq.
  rewrite runLocal_idem.
  equality.
  rewrite <- Heq.
  rewrite runLocal_idem.
  rewrite Heq.
  equality.
Qed.

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

Theorem two_increments_ok_again :
  invariantFor (trsys_of $0 {} two_increments)
               (fun p => let '(_, _, c) := p in
                         notAboutToFail c = true).
Proof.
Admitted.
(*  apply step_stepL.
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
Qed.*)


(** * Optimization #2: partial-order reduction *)

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

Theorem independent_threads_ok :
  invariantFor (trsys_of $0 {} independent_threads)
               (fun p => let '(_, _, c) := p in
                         notAboutToFail c = true).
Proof.
Admitted.
(*  apply step_stepL.
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
Qed.*)

Record summary := {
  Reads : set nat;
  Writes : set nat;
  Locks : set nat
}.

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

Inductive summarizeThreads : cmd -> list (cmd * summary) -> Prop :=
| StPar : forall c1 c2 ss1 ss2,
    summarizeThreads c1 ss1
    -> summarizeThreads c2 ss2
    -> summarizeThreads (Par c1 c2) (ss1 ++ ss2)
| StAtomic : forall c s,
    summarize c s
    -> summarizeThreads c [(c, s)].

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

Inductive stepC : heap * locks * list (cmd * summary) -> heap * locks * list (cmd * summary) -> Prop :=
| StepDone : forall h l r s cs1 cs2,
   stepC (h, l, cs1 ++ (Return r, s) :: cs2) (h, l, cs1 ++ cs2)
| StepFirst : forall h l c h' l' c' s cs,
  step (h, l, c) (h', l', c')
  -> stepC (h, l, (c, s) :: cs) (h', l', (c', s) :: cs)
| StepAny : forall h l c h' l' s cs1 c1 s1 cs2 c1',
  (forall c0 h'' l'' c'', nextAction c c0
                          -> List.Forall (fun c_s => commutes c0 (snd c_s)) (cs1 ++ (c1, s1) :: cs2)
                          -> step (h, l, c) (h'', l'', c'')
                          -> False)
  -> step (h, l, c1) (h', l', c1')
  -> stepC (h, l, (c, s) :: cs1 ++ (c1, s1) :: cs2) (h', l', (c, s) :: cs1 ++ (c1', s1) :: cs2).

Definition trsys_ofC (h : heap) (l : locks) (cs : list (cmd * summary)) := {|
  Initial := {(h, l, cs)};
  Step := stepC
|}.


Lemma commutes_sound : forall h l c2 h' l' c2',
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

Hint Constructors summarize.

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

Fixpoint pow2 (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => pow2 n' * 2
  end.

Inductive boundRunningTime : cmd -> nat -> Prop :=
| BrtReturn : forall r,
    boundRunningTime (Return r) 0
| BrtFail :
    boundRunningTime Fail 0
| BrtRead : forall a,
    boundRunningTime (Read a) 1
| BrtWrite : forall a v,
    boundRunningTime (Write a v) 1
| BrtLock : forall a,
    boundRunningTime (Lock a) 1
| BrtUnlock : forall a,
    boundRunningTime (Unlock a) 1
| BrtBind : forall c1 c2 n1 n2,
    boundRunningTime c1 n1
    -> (forall r, boundRunningTime (c2 r) n2)
    -> boundRunningTime (Bind c1 c2) (S (n1 + n2))
| BrtPar : forall c1 c2 n1 n2,
    boundRunningTime c1 n1
    -> boundRunningTime c2 n2
    -> boundRunningTime (Par c1 c2) (pow2 (n1 + n2)).

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

  invert H.
  simplify.
  eauto.
Qed.

Require Import Classical.

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
  cases x1.
  do 3 eexists; propositional.
  apply trc_one.
  eauto.
  eauto.
  do 3 eexists; propositional.
  eauto.
  invert H; eauto.
  do 3 eexists; propositional.
  eauto.
  invert H; eauto.
  do 3 eexists; propositional.
  eauto.
  invert H; eauto.
  do 3 eexists; propositional.
  eauto.
  invert H; eauto.
  do 3 eexists; propositional.
  eauto.
  invert H; eauto.
  do 3 eexists; propositional.
  eauto.
  invert H; eauto.
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

Lemma translate_trace : forall h l c h' l' c',
    step^* (h, l, c) (h', l', c')
    -> (forall h'' l'' c'', step (h', l', c') (h'', l'', c'') -> False)
    -> notAboutToFail c' = false
    -> forall cs, summarizeThreads c cs
    -> exists h' l' cs', stepC^* (h, l, cs) (h', l', cs')
                         /\ Exists (fun c_s => notAboutToFail (fst c_s) = false) cs'.
Proof.
Admitted.

Lemma Forall_Exists_contra : forall A (f : A -> bool) ls,
    Exists (fun x => f x = false) ls
    -> Forall (fun x => f x = true) ls
    -> False.
Proof.
  induct 1; invert 1; equality.
Qed.

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
  eapply translate_trace in H7; eauto.
  first_order.
  apply H1 in H7; auto.
  eapply Forall_Exists_contra.
  apply H9.
  assumption.
Qed.
