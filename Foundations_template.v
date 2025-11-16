Require Import Frap.
From Stdlib Require Import ZArith.

(** * Simulating System F *)

(* We will actually replace [Type] from the book with [Prop] here to get
 * impredicativity. *)

Definition nat : Prop :=
  forall A : Prop, (A -> A) -> A -> A.
Definition zero : nat :=
  fun (A : Prop) (f : A -> A) (x : A) => x.
Definition plus1 : nat -> nat :=
  fun (n : nat) (A : Prop) (f : A -> A) (x : A) => f (n A f x).
Definition add : nat -> nat -> nat :=
  fun (n m : nat) => n nat plus1 m.
Definition mult : nat -> nat -> nat :=
  fun (n m : nat) => n nat (add m) zero.

Goal mult (plus1 zero) (add (plus1 (plus1 zero)) (plus1 zero))
     = plus1 (plus1 (plus1 zero)).
Proof.
  reflexivity.
Qed.
(* Note that, all along, the tactic [reflexivity] has applied a decidable
 * definitional equality like the ones we formalize in this chapter, explaining
 * its ability to do some computation on our behalf. *)

Definition True : Prop :=
  forall A : Prop, A -> A.
Definition I : True :=
  fun (A : Prop) (x : A) => x.

Definition False : Prop :=
  forall A : Prop, A.
Definition False_elim : False -> forall A : Prop, A :=
  fun x : False => x.


(** * Simulating System Fomega *)

Definition and : Prop -> Prop -> Prop :=
  fun A1 A2 : Prop => forall A : Prop, (A1 -> A2 -> A) -> A.
Definition and_intro : forall A1 A2 : Prop, A1 -> A2 -> and A1 A2 :=
  fun (A1 A2 : Prop) (x1 : A1) (x2 : A2)
      (A : Prop) (f : A1 -> A2 -> A) => f x1 x2.
Definition and_elim1 : forall A1 A2 : Prop, and A1 A2 -> A1 :=
  fun (A1 A2 : Prop) (x : and A1 A2) =>
    x A1 (fun (x1 : A1) (x2 : A2) => x1).
Definition and_elim2 : forall A1 A2 : Prop, and A1 A2 -> A2 :=
  fun (A1 A2 : Prop) (x : and A1 A2) =>
    x A2 (fun (x1 : A1) (x2 : A2) => x2).

(* Example of the encoding in action: *)
Definition and_comm (A B : Prop) (p : and A B) : and B A.
Admitted.

Definition or : Prop -> Prop -> Prop :=
  fun A1 A2 : Prop => forall A : Prop, (A1 -> A) -> (A2 -> A) -> A.
Definition or_intro1 : forall A1 A2 : Prop, A1 -> or A1 A2 :=
  fun (A1 A2 : Prop) (x1 : A1)
      (A : Prop) (f1 : A1 -> A) (f2 : A2 -> A) => f1 x1.
Definition or_intro2 : forall A1 A2 : Prop, A2 -> or A1 A2 :=
  fun (A1 A2 : Prop) (x2 : A2)
      (A : Prop) (f1 : A1 -> A) (f2 : A2 -> A) => f2 x2.
Definition or_elim : forall A1 A2 : Prop, or A1 A2
  -> forall A : Prop, (A1 -> A) -> (A2 -> A) -> A :=
  fun (A1 A2 : Prop) (x : or A1 A2) => x.

(* Example of the encoding in action: *)
Definition or_comm (A B : Prop) (p : or A B) : or B A.
Admitted.


(** * Simulating the Calculus of Constructions *)

Definition ex : forall a : Set, (a -> Prop) -> Prop :=
  fun (a : Set) (f : a -> Prop) => forall A : Prop, (forall x : a, f x -> A) -> A.
Definition ex_intro : forall (a : Set) (f : a -> Prop) (v : a), f v -> ex a f :=
  fun (a : Set) (f : a -> Prop) (x : a) (y : f x) (A : Prop)
      (k : forall x : a, f x -> A) => k x y.
Definition ex_elim : forall (a : Set) (f : a -> Prop), ex a f
  -> forall A : Prop, (forall x : a, f x -> A) -> A :=
  fun (a : Set) (f : a -> Prop) (x : ex a f) => x.

(* Example of the encoding in action: *)
Definition quant_commute (a : Set) (f : a -> a -> Prop)
           (p : ex a (fun x => forall y : a, f x y))
  : forall y : a, ex a (fun x => f x y).
Admitted.

Definition eq : forall a : Set, a -> a -> Prop :=
  fun (a : Set) (x y : a) => forall f : a -> Prop, f x -> f y.
Definition eq_refl : forall (a : Set) (x : a), eq a x x :=
  fun (a : Set) (x : a) (f : a -> Prop) (p : f x) => p.
Definition eq_sym : forall (a : Set) (x y : a), eq a x y -> eq a y x :=
  fun (a : Set) (x y : a) (e : eq a x y) =>
    e (fun v : a => eq a v x) (eq_refl a x).


(** * Illustrating Rocq's own rules for inductive definitions *)

(** ** Strict positivity *)

Fail Inductive Omega : Set :=
| Make (_ : Omega -> False).

Section Omega.
  Variable Omega : Set.
  Variable Make : (Omega -> False) -> Omega.
  Variable Out : Omega -> (Omega -> False).

  Definition contra : False.
  Admitted.
End Omega.

(** * Universe levels in constructor arguments *)

Inductive dyn : Type :=
| Dyn (A : Type) (v : A).

Definition zero' : dyn := Dyn nat zero.
Fail Definition zero'' : dyn := Dyn dyn zero'.
(* Universe inconsistency!  The relevant check is working.
 * Note how the error message reveals that Rocq internally is tracking universe
 * levels, though we get to write [Type] without levels. *)

(** * Large eliminations *)

Inductive exists_positive (P : Z -> Prop) : Prop :=
| ExP (x : Z) (pos : (x > 0)%Z) (p : P x).

Definition exists_positive_to_exists (P : Z -> Prop) (e : exists_positive P) : ex Z P :=
  match e with
  | ExP _ x _ p => ex_intro Z P x p
  end.

Fail Definition exists_positive_out (P : Z -> Prop) (e : exists_positive P) : Z :=
  match e with
  | ExP _ x _ _ => x
  end.
(* Technically, this one isn't really a large elimination.  The problem we run
 * into here is a restriction on information flow from from proofs into
 * non-[Prop] universes, so that extraction can work properly despite erasing
 * proofs. *)

Fail Definition exists_positive_out (P : Z -> Prop) (e : exists_positive P) : Type :=
  match e with
  | ExP _ _ _ _ => dyn
  end.
(* This one is a true large elimination. *)


(** * Seeing what the Rocq proof engine is up to *)

Goal (exists n : Z, n > 0 /\ n > 1)%Z.
Proof.
  eexists.
  split.
  Show Existentials.
  (* Note one existential for [n] and two for the open subgoals. *)
Abort.

(* This next theorem is false!  Let's see how Rocq helps us avoid a bogus
 * proof. *)
Goal forall (A B : Set) (P : A -> B -> Prop),
    (forall x : A, exists y : B, P x y) -> (exists y : B, forall x : A, P x y).
Proof.
  intros.
  eexists.
  intro.
  specialize (H x).
  invert H.
  Fail apply H0.
  (* Phew!  This step failed. *)
  Show Existentials.
  (* Now we can see that [?y] exists in a context that doesn't contain [x0],
   * hence our inability to instantiate [?y = x0]. *)
Abort.
