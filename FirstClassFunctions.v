(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Supplementary Coq material: first-class functions and continuations
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.


(** * Classic list functions *)

Fixpoint map {A B : Set} (f : A -> B) (ls : list A) : list B :=
  match ls with
  | nil => nil
  | x :: ls' => f x :: map f ls'
  end.

Fixpoint filter {A : Set} (f : A -> bool) (ls : list A) : list A :=
  match ls with
  | nil => nil
  | x :: ls' => if f x then x :: filter f ls' else filter f ls'
  end.

Fixpoint foldl {A B : Set} (f : A -> B -> B) (acc : B) (ls : list A) : B :=
  match ls with
  | nil => acc
  | x :: ls' => foldl f (f x acc) ls'
  end.

Record programming_languages := {
  Name : string;
  PurelyFunctional : bool;
  AppearedInYear : nat
}.

Definition pascal := {|
  Name := "Pascal";
  PurelyFunctional := false;
  AppearedInYear := 1970
|}.

Definition c := {|
  Name := "C";
  PurelyFunctional := false;
  AppearedInYear := 1972
|}.

Definition gallina := {|
  Name := "Gallina";
  PurelyFunctional := true;
  AppearedInYear := 1989
|}.

Definition haskell := {|
  Name := "Haskell";
  PurelyFunctional := true;
  AppearedInYear := 1990
|}.

Definition ocaml := {|
  Name := "OCaml";
  PurelyFunctional := false;
  AppearedInYear := 1996
|}.

Definition languages := [pascal; c; gallina; haskell; ocaml].

Compute map Name languages.
Compute map Name (filter PurelyFunctional languages).
Compute foldl max 0 (map AppearedInYear languages).
Compute foldl max 0 (map AppearedInYear (filter PurelyFunctional languages)).

