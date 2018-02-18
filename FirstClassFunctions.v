(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Supplementary Coq material: first-class functions and continuations
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.


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

Record programming_language := {
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


(** * The classics in continuation-passing style *)

Fixpoint mapK {A B R : Set} (f : A -> (B -> R) -> R) (ls : list A) (k : list B -> R) : R :=
  match ls with
  | nil => k nil
  | x :: ls' => f x (fun x' => mapK f ls' (fun ls'' => k (x' :: ls'')))
  end.

Fixpoint filterK {A R : Set} (f : A -> (bool -> R) -> R) (ls : list A) (k : list A -> R) : R :=
  match ls with
  | nil => k nil
  | x :: ls' => f x (fun b => filterK f ls' (fun ls'' => k (if b then x :: ls'' else ls'')))
  end.

Fixpoint foldlK {A B R : Set} (f : A -> B -> (B -> R) -> R) (acc : B) (ls : list A) (k : B -> R) : R :=
  match ls with
  | nil => k acc
  | x :: ls' => f x acc (fun x' => foldlK f x' ls' k)
  end.

Definition NameK {R : Set} (l : programming_language) (k : string -> R) : R :=
  k (Name l).
Definition PurelyFunctionalK {R : Set} (l : programming_language) (k : bool -> R) : R :=
  k (PurelyFunctional l).
Definition AppearedInYearK {R : Set} (l : programming_language) (k : nat -> R) : R :=
  k (AppearedInYear l).
Definition maxK {R : Set} (n1 n2 : nat) (k : nat -> R) : R :=
  k (max n1 n2).

Compute mapK NameK languages (fun ls => ls).
Compute filterK PurelyFunctionalK languages (fun ls => mapK NameK ls (fun x => x)).
Compute mapK AppearedInYearK languages (fun ls => foldlK maxK 0 ls (fun x => x)).
Compute filterK PurelyFunctionalK languages
        (fun ls1 => mapK AppearedInYearK ls1
                         (fun ls2 => foldlK maxK 0 ls2 (fun x => x))).

Theorem mapK_ok : forall {A B R : Set} (f : A -> (B -> R) -> R) (f_base : A -> B),
    (forall x k, f x k = k (f_base x))
    -> forall (ls : list A) (k : list B -> R),
      mapK f ls k = k (map f_base ls).
Proof.
  induct ls; simplify; try equality.

  rewrite H.
  apply IHls.
Qed.

Theorem names_ok : forall langs,
    mapK NameK langs (fun ls => ls) = map Name langs.
Proof.
  simplify.
  apply mapK_ok with (f_base := Name).
  unfold NameK.
  trivial.
Qed.

Theorem filterK_ok : forall {A R : Set} (f : A -> (bool -> R) -> R) (f_base : A -> bool),
    (forall x k, f x k = k (f_base x))
    -> forall (ls : list A) (k : list A -> R),
      filterK f ls k = k (filter f_base ls).
Proof.
  induct ls; simplify; try equality.

  rewrite H.
  apply IHls.
Qed.

Theorem purenames_ok : forall langs,
    filterK PurelyFunctionalK langs (fun ls => mapK NameK ls (fun x => x))
    = map Name (filter PurelyFunctional langs).
Proof.
  simplify.
  rewrite filterK_ok with (f_base := PurelyFunctional); trivial.
  apply mapK_ok with (f_base := Name); trivial.
Qed.

Theorem foldlK_ok : forall {A B R : Set} (f : A -> B -> (B -> R) -> R) (f_base : A -> B -> B),
    (forall x acc k, f x acc k = k (f_base x acc))
    -> forall (ls : list A) (acc : B) (k : B -> R),
      foldlK f acc ls k = k (foldl f_base acc ls).
Proof.
  induct ls; simplify; try equality.

  rewrite H.
  apply IHls.
Qed.

Theorem latest_ok : forall langs,
    mapK AppearedInYearK langs (fun ls => foldlK maxK 0 ls (fun x => x))
    = foldl max 0 (map AppearedInYear langs).
Proof.
  simplify.
  rewrite mapK_ok with (f_base := AppearedInYear); trivial.
  apply foldlK_ok with (f_base := max); trivial.
Qed.

Theorem latestpure_ok : forall langs,
    filterK PurelyFunctionalK langs
            (fun ls1 => mapK AppearedInYearK ls1
                             (fun ls2 => foldlK maxK 0 ls2 (fun x => x)))
    = foldl max 0 (map AppearedInYear (filter PurelyFunctional langs)).
Proof.
  simplify.
  rewrite filterK_ok with (f_base := PurelyFunctional); trivial.
  rewrite mapK_ok with (f_base := AppearedInYear); trivial.
  apply foldlK_ok with (f_base := max); trivial.
Qed.
