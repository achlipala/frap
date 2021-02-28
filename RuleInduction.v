(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * New chapter: inductive relations and rule induction
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.


(** * Finite sets as inductive predicates *)

Inductive my_favorite_numbers : nat -> Prop :=
| ILike17 : my_favorite_numbers 17
| ILike23 : my_favorite_numbers 23
| ILike42 : my_favorite_numbers 42.

Check my_favorite_numbers_ind.

Theorem favorites_below_50 : forall n, my_favorite_numbers n -> n < 50.
Proof.
  simplify.
  invert H.
  linear_arithmetic.
  linear_arithmetic.
  linear_arithmetic.
Qed.


(** * Transitive closure of relations *)

Inductive tc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TcBase : forall x y, R x y -> tc R x y
| TcTrans : forall x y z, tc R x y -> tc R y z -> tc R x z.

(** ** Less-than reimagined *)

Definition oneApart (n m : nat) : Prop :=
  n + 1 = m.

Definition lt' : nat -> nat -> Prop := tc oneApart.

Theorem lt'_lt : forall n m, lt' n m -> n < m.
Proof.
  induct 1.

  unfold oneApart in H.
  linear_arithmetic.

  linear_arithmetic.
Qed.

Lemma lt'_O_S : forall m, lt' 0 (S m).
Proof.
  induct m; simplify.

  apply TcBase.
  unfold oneApart.
  linear_arithmetic.

  apply TcTrans with (S m).
  assumption.
  apply TcBase.
  unfold oneApart.
  linear_arithmetic.
Qed.

Lemma lt_lt'' : forall n k, lt' n (S k + n).
Proof.
  induct k; simplify.

  apply TcBase.
  unfold oneApart.
  linear_arithmetic.

  apply TcTrans with (S (k + n)).
  assumption.
  apply TcBase.
  unfold oneApart.
  linear_arithmetic.
Qed.
  
Theorem lt_lt' : forall n m, n < m -> lt' n m.
Proof.
  simplify.
  replace m with (S (m - n - 1) + n) by linear_arithmetic.
  apply lt_lt''.
Qed.

(** ** Transitive closure is idempotent. *)

Theorem tc_tc2 : forall A (R : A -> A -> Prop) x y, tc R x y -> tc (tc R) x y.
Proof.
  induct 1.

  apply TcBase.
  apply TcBase.
  assumption.

  apply TcTrans with y.
  assumption.
  assumption.
Qed.

Theorem tc2_tc : forall A (R : A -> A -> Prop) x y, tc (tc R) x y -> tc R x y.
Proof.
  induct 1.

  assumption.

  apply TcTrans with y.
  assumption.
  assumption.
Qed.


(** * Permutation *)

(* Lifted from the Coq standard library: *)
Inductive Permutation {A} : list A -> list A -> Prop :=
| perm_nil :
    Permutation [] []
| perm_skip : forall x l l',
    Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap : forall x y l,
    Permutation (y::x::l) (x::y::l)
| perm_trans : forall l l' l'',
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Lemma Permutation_to_front : forall A (a : A) (ls : list A),
    Permutation (a :: ls) (ls ++ [a]).
Proof.
  induct ls; simplify.

  apply perm_skip.
  apply perm_nil.

  apply perm_trans with (a0 :: a :: ls).
  apply perm_swap.
  apply perm_skip.
  assumption.
Qed.

Theorem Permutation_rev : forall A (ls : list A),
    Permutation ls (rev ls).
Proof.
  induct ls; simplify.

  apply perm_nil.

  apply perm_trans with (a :: rev ls).
  apply perm_skip.
  assumption.
  apply Permutation_to_front.
Qed.

Theorem Permutation_length : forall A (ls1 ls2 : list A),
    Permutation ls1 ls2 -> length ls1 = length ls2.
Proof.
  induct 1; simplify.

  equality.

  equality.

  equality.

  equality.
Qed.

Lemma Permutation_app' : forall A (ls ls1 ls2 : list A),
    Permutation ls1 ls2
    -> Permutation (ls ++ ls1) (ls ++ ls2).
Proof.
  induct ls; simplify.

  assumption.

  apply perm_skip.
  apply IHls.
  assumption.
Qed.

Lemma Permutation_refl : forall A (ls : list A),
    Permutation ls ls.
Proof.
  induct ls.

  apply perm_nil.

  apply perm_skip.
  assumption.
Qed.

Theorem Permutation_app : forall A (ls1 ls1' : list A),
    Permutation ls1 ls1'
    -> forall ls2 ls2', Permutation ls2 ls2'
    -> Permutation (ls1 ++ ls2) (ls1' ++ ls2').
Proof.
  induct 1; simplify.

  assumption.

  apply perm_skip.
  apply IHPermutation.
  assumption.

  apply perm_trans with (x :: y :: l ++ ls2).
  apply perm_swap.
  apply perm_skip.
  apply perm_skip.
  apply Permutation_app'.
  assumption.

  apply perm_trans with (l' ++ ls2').
  apply IHPermutation1.
  assumption.
  apply IHPermutation2.
  
  apply Permutation_refl.
Qed.
