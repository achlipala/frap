(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 12: Separation Logic
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


(** * Encore of last mixed-embedding language from last time *)

Inductive loop_outcome acc :=
| Done (a : acc)
| Again (a : acc).

Inductive cmd : Set -> Type :=
| Return {result : Set} (r : result) : cmd result
| Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Read (a : nat) : cmd nat
| Write (a v : nat) : cmd unit
| Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc
| Fail {result} : cmd result

(* But let's also add memory allocation and deallocation. *)
| Alloc (numWords : nat) : cmd nat
| Free (base numWords : nat) : cmd unit.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).

(* These helper functions respectively initialize a new span of memory and
 * remove a span of memory that the program is done with. *)

Fixpoint initialize (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => initialize h base numWords' $+ (base + numWords', 0)
  end.

Fixpoint deallocate (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => deallocate h base numWords' $- (base + numWords')
  end.

(* Let's do the semantics a bit differently this time, falling back on classic
 * small-step operational semantics. *)
Inductive step : forall A, heap * cmd A -> heap * cmd A -> Prop :=
| StepBindRecur : forall result result' (c1 c1' : cmd result') (c2 : result' -> cmd result) h h',
  step (h, c1) (h', c1')
  -> step (h, Bind c1 c2) (h', Bind c1' c2)
| StepBindProceed : forall (result result' : Set) (v : result') (c2 : result' -> cmd result) h,
  step (h, Bind (Return v) c2) (h, c2 v)

| StepLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)) h,
  step (h, Loop init body) (h, o <- body init; match o with
                                               | Done a => Return a
                                               | Again a => Loop a body
                                               end)

| StepRead : forall h a v,
  h $? a = Some v
  -> step (h, Read a) (h, Return v)
| StepWrite : forall h a v v',
  h $? a = Some v
  -> step (h, Write a v') (h $+ (a, v'), Return tt)
| StepAlloc : forall h numWords a,
  (forall i, i < numWords -> h $? (a + i) = None)
  -> step (h, Alloc numWords) (initialize h a numWords, Return a)
| StepFree : forall h a numWords,
  step (h, Free a numWords) (deallocate h a numWords, Return tt).


Definition trsys_of (h : heap) {result} (c : cmd result) := {|
  Initial := {(h, c)};
  Step := step (A := result)
|}.
