(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Supplementary Rocq material: subset types
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/
  * Much of the material comes from CPDT <http://adam.chlipala.net/cpdt/> by the same author. *)

Require Import FrapWithoutSets.
(* We import a pared-down version of the book library, to avoid notations that
 * clash with some we want to use here. *)

Set Implicit Arguments.
Set Asymmetric Patterns.


(** * Introducing Subset Types *)

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

From Stdlib Require Extraction.
Extraction pred.














(** * Decidable Proposition Types *)

Print sumbool.

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

Definition eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Admitted.

Compute eq_nat_dec 2 2.
Compute eq_nat_dec 2 3.

Extraction eq_nat_dec.









Section In_dec.
  Variable A : Set.
  Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  (* The final function is easy to write using the techniques we have developed
   * so far. *)

  Definition In_dec : forall (x : A) (ls : list A), {In x ls} + {~ In x ls}.
  Admitted.
End In_dec.

Compute In_dec eq_nat_dec 2 (1 :: 2 :: nil).
Compute In_dec eq_nat_dec 3 (1 :: 2 :: nil).

Extraction In_dec.













(** * Partial Subset Types *)

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).











Print sumor.

Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).










(** * Monadic Notations *)

Notation "x <- e1 ; e2" := (match e1 with
                            | Unknown => ??
                            | Found x _ => e2
                           end)
(right associativity, at level 60).

Definition doublePred : forall n1 n2 : nat, {{p | n1 = S (fst p) /\ n2 = S (snd p)}}.
Admitted.













Notation "x <-- e1 ; e2" := (match e1 with
                             | inright _ => !!
                             | inleft (exist x _) => e2
                             end)
(right associativity, at level 60).

Definition doublePred' : forall n1 n2 : nat,
  {p : nat * nat | n1 = S (fst p) /\ n2 = S (snd p)}.
Admitted.
















(** * A Type-Checking Example *)

Inductive exp :=
| Nat (n : nat)
| Plus (e1 e2 : exp)
| Bool (b : bool)
| And (e1 e2 : exp).

Inductive type := TNat | TBool.

Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n,
  hasType (Nat n) TNat
| HtPlus : forall e1 e2,
  hasType e1 TNat
  -> hasType e2 TNat
  -> hasType (Plus e1 e2) TNat
| HtBool : forall b,
  hasType (Bool b) TBool
| HtAnd : forall e1 e2,
  hasType e1 TBool
  -> hasType e2 TBool
  -> hasType (And e1 e2) TBool.

Definition typeCheck : forall e : exp, {{t | hasType e t}}.
Admitted.

Compute typeCheck (Nat 0).
Compute typeCheck (Plus (Nat 1) (Nat 2)).
Compute typeCheck (Plus (Nat 1) (Bool false)).

Extraction typeCheck.
