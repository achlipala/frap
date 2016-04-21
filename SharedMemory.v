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

(* Now here's the new part: parallel composition of commands. *)
| Par (c1 c2 : cmd unit) : cmd unit

(* Let's also add locking commands, where locks are named by [nat]s. *)
| Lock (a : nat) : cmd unit
| Unlock (a : nat) : cmd unit.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).
Infix "||" := Par.

Definition locks := set nat.

Inductive step : forall A, heap * locks * cmd A -> heap * locks * cmd A -> Prop :=
| StepBindRecur : forall result result' (c1 c1' : cmd result') (c2 : result' -> cmd result) h h' l l',
  step (h, l, c1) (h', l', c1')
  -> step (h, l, Bind c1 c2) (h', l', Bind c1' c2)
| StepBindProceed : forall (result result' : Set) (v : result') (c2 : result' -> cmd result) h l,
  step (h, l, Bind (Return v) c2) (h, l, c2 v)

| StepLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)) h l,
  step (h, l, Loop init body) (h, l, o <- body init; match o with
                                                     | Done a => Return a
                                                     | Again a => Loop a body
                                                     end)

| StepRead : forall h l a,
  step (h, l, Read a) (h, l, Return (h $! a))
| StepWrite : forall h l a v,
  step (h, l, Write a v) (h $+ (a, v), l, Return tt)

| StepParRecur1 : forall h l c1 c2 h' l' c1',
  step (h, l, c1) (h', l', c1')
  -> step (h, l, Par c1 c2) (h', l', Par c1' c2)
| StepParRecur2 : forall h l c1 c2 h' l' c2',
  step (h, l, c2) (h', l', c2')
  -> step (h, l, Par c1 c2) (h', l', Par c1 c2')
| StepParProceed1 : forall h l c2,
   step (h, l, Par (Return tt) c2) (h, l, c2)
| StepParProceed2 : forall h l c1,
   step (h, l, Par c1 (Return tt)) (h, l, c1)

| StepLock : forall h l a,
  ~a \in l
  -> step (h, l, Lock a) (h, l \cup {a}, Return tt)
| StepUnlock : forall h l a,
  a \in l
  -> step (h, l, Unlock a) (h, l \setminus {a}, Return tt).

Definition trsys_of (h : heap) (l : locks) {result} (c : cmd result) := {|
  Initial := {(h, l, c)};
  Step := step (A := result)
|}.
