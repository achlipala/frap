(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Supplementary Coq material: polymorphism and generic data structures
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.
(* This command sets up automatic inference of tedious arguments. *)

(* One of the recurring ingredients in effective machine formalization is data
 * structures, and, as in general programming, we want to be able to define data
 * structures that are *generic* in the kinds of data they contain.  Coq
 * supports such things in roughly the same way as Haskell and OCaml, via
 * *parametric polymorphism*, which is closely related to the idea of *generics*
 * in languages like Java. *)

(* Our first example: the [option] type family.  While Java and friends force
 * all sorts of different types to include the special value [null], in Coq we
 * request that option explicitly by wrapping a type in [option].  Specifically,
 * any value of type [option A], for some type [A], is either [None] (sort of
 * like [null]) or [Some v] for a [v] of type [A]. *)
Inductive option (A : Set) : Set :=
| None
| Some (v : A).

Arguments None [A].
(* This command asks Coq to *infer* the [A] type for each specific use of
 * [None]. *)

(* Here are a few example terms using [option]. *)
Example no_number : option nat := None.
Example a_number : option nat := Some 42.
Example no_number_squared : option (option nat) := None.
Example no_number_squared_inside : option (option nat) := Some None.
Example a_number_squared : option (option nat) := Some (Some 42).

(* Pattern matching is the key ingredient for working with inductive definitions
 * of all sorts.  Here are some examples matching on [option]s. *)

Definition increment_optional (no : option nat) : option nat :=
  match no with
  | None => None
  | Some n => Some (n + 1)
  end.

(* Here we use type [A * B] of *pairs*, inhabited by values [(a, b)], with
 * [a : A] and [b : B]. *)
Definition add_optional (po : option (nat * nat)) : option nat :=
  match po with
  | None => None
  | Some (n, m) => Some (n + m)
  end.


(** * Lists *)

(* For functional programming (as in Coq), the king of all generic data
 * structures is the *list*, which you explored a bit in the first problem set.
 * Let's recap that type definition. *)
Inductive list (A : Set) : Set :=
| nil
| cons (hd : A) (tl : list A).

Arguments nil [A].

(* [nil] is the empty list, while [cons], standing for "construct," extends a
 * list of length [n] into one of length [n+1]. *)

(* Here are some simple lists. *)

Example nats0 : list nat := nil.
Example nats1 : list nat := cons 1 nil.
Example nats2 : list nat := cons 1 (cons 2 nil).

(* Coq features a wonderful notation system, to help us write more concise and
 * readable code after introducing new syntactic forms.  We will not give a
 * systematic presentation of the notation system, but we will show many
 * examples, from which it is possible to infer generality by scientific
 * induction.  And, of course, the interested reader can always check the
 * notations chapter of the Coq reference manual. *)

(* First, our examples can get more readable with an infix operator for [cons]. *)

Infix "::" := cons.

Example nats1' : list nat := 1 :: nil.
Example nats2' : list nat := 1 :: 2 :: nil.

(* Getting even more fancy, we declare a notation for list literals. *)

Notation "[ ]" := nil.
Notation "[ x1 ; .. ; xN ]" := (cons x1 (.. (cons xN nil) ..)).

Example nats0'' : list nat := [].
Example nats1'' : list nat := [1].
Example nats2'' : list nat := [1; 2].
Example nats3'' : list nat := [1; 2; 3].

(* Here are some classic recursive functions that operate over lists.
 * First, here is how to compute the length of a list.  Recall that we put
 * *implicit* function arguments in curly braces, asking Coq to infer them at
 * call sites. *)

Fixpoint length {A} (ls : list A) : nat :=
  match ls with
  | nil => 0
  | _ :: ls' => 1 + length ls'
  end.

(* The first problem set involved an exercise with list append and reverse
 * operations.  To avoid spoiling the proofs there about those functions, we
 * will give their definitions here without proving the classic theorems from
 * the problem set. *)

Fixpoint app {A} (ls1 ls2 : list A) : list A :=
  match ls1 with
  | nil => ls2
  | x :: ls1' => x :: app ls1' ls2
  end.

Infix "++" := app.

Fixpoint rev {A} (ls : list A) : list A :=
  match ls with
  | nil => nil
  | x :: ls' => rev ls' ++ [x]
  end.

(* One of the classic gotchas in functional-programming class is how slow this
 * naive [rev] is.  Each [app] operation requires linear time, so running
 * linearly many [app]s brings us to quadratic time for [rev].  Using a helper
 * function, we can bring [rev] to its optimal linear time. *)

Fixpoint rev_append {A} (ls acc : list A) : list A :=
  match ls with
  | nil => acc
  | x :: ls' => rev_append ls' (x :: acc)
  end.

(* This function [rev_append] takes an extra *accumulator* argument, in which we
 * gradually build up the original input in reversed order.  The base case just
 * returns the accumulator.  Now reversal just needs to do a [rev_append] with
 * an empty initial accumulator. *)

Definition rev' {A} (ls : list A) : list A :=
  rev_append ls [].

(* A few test cases can help convince us that this seems to work. *)

Compute rev [1; 2; 3; 4].
Compute rev' [1; 2; 3; 4].
Compute rev ["hi"; "bye"; "sky"].
Compute rev' ["hi"; "bye"; "sky"].

(* OK, great.  Now it seems worth investing in a correctness proof.  We'll
 * discover it interactively in class, but here's a worked-out final
 * answer, with the several lemmas that we discover are useful. *)

(* List concatenation is associative. *)
Lemma app_assoc : forall A (ls1 ls2 ls3 : list A),
    (ls1 ++ ls2) ++ ls3 = ls1 ++ (ls2 ++ ls3).
Proof.
  induct ls1; simplify.

  equality.

  rewrite IHls1.
  equality.
Qed.

(* The natural correctness condition for [rev_append]: it does what it says on
 * the package, combining reversal with appending! *)
Lemma rev_append_ok : forall A (ls acc : list A),
    rev_append ls acc = rev ls ++ acc.
Proof.
  induct ls; simplify.

  equality.

  rewrite IHls.
  simplify.
  rewrite app_assoc.
  simplify.
  equality.
Qed.

(* Concatenating the empty list has no effect. *)
Lemma app_nil : forall A (ls : list A),
    ls ++ [] = ls.
Proof.
  induct ls; simplify.

  equality.

  equality.
Qed.

(* Now we can prove equivalence of [rev'] and [rev], with no new induction. *)
Theorem rev'_ok : forall A (ls : list A),
    rev' ls = rev ls.
Proof.
  simplify.
  unfold rev'.
  rewrite rev_append_ok.
  apply app_nil.
Qed.
