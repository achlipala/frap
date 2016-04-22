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
  model_check_step.
  model_check_step.
  model_check_step.
  model_check_done.

  simplify.
  propositional; subst; equality.
Qed.


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
