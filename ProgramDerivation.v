(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 16: Deriving Programs from Specifications
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/
  * Some material borrowed from Fiat <http://plv.csail.mit.edu/fiat/> *)

Require Import FrapWithoutSets.
Require Import Program Setoids.Setoid Classes.RelationClasses Classes.Morphisms Morphisms_Prop.


(** * The computation monad *)

Definition comp (A : Type) := A -> Prop.

Definition ret {A} (x : A) : comp A := eq x.
Definition bind {A B} (c1 : comp A) (c2 : A -> comp B) : comp B :=
  fun b => exists a, c1 a /\ c2 a b.
Definition pick_ {A} (P : A -> Prop) : comp A := P.

Definition refine {A} (c1 c2 : comp A) :=
  forall a, c2 a -> c1 a.

Ltac morphisms := unfold refine, impl, pointwise_relation, bind; hnf; first_order.

Global Instance refine_PreOrder A : PreOrder (@refine A).
Proof.
  constructor; morphisms.
Qed.

Add Parametric Morphism A : (@refine A)
    with signature (@refine A) --> (@refine A) ++> impl
      as refine_refine.
Proof.
  morphisms.
Qed.

Add Parametric Morphism A B : (@bind A B)
    with signature (@refine A) 
                     ==> (pointwise_relation _ (@refine B))
                     ==> (@refine B)
    as refine_bind.
Proof.
  morphisms.
Qed.

Add Parametric Morphism A B : (@bind A B)
    with signature (flip (@refine A))
                     ==> (pointwise_relation _ (flip (@refine B)))
                     ==> (flip (@refine B))
      as refine_bind_flip.
Proof.
  morphisms.
Qed.

Theorem bind_ret : forall A B (v : A) (c2 : A -> comp B),
    refine (bind (ret v) c2) (c2 v).
Proof.
  morphisms.
Qed.

Notation "'pick' x 'where' P" := (pick_ (fun x => P)) (at level 80, x at level 0).
Notation "x <- c1 ; c2" := (bind c1 (fun x => c2)) (at level 81, right associativity).


(** * Picking a number not in a list *)

(* A specification of what it means to choose a number that is not in a
 * particular list *)
Definition notInList (ls : list nat) :=
  pick n where ~In n ls.

(* We can use a simple property to justify a decomposition of the original
 * spec. *)
Theorem notInList_decompose : forall ls,
  refine (notInList ls) (upper <- pick upper where forall n, In n ls -> upper >= n;
                         pick beyond where beyond > upper).
Proof.
  simplify.
  unfold notInList, refine, bind, pick_, not.
  first_order.
  apply H in H0.
  linear_arithmetic.
Qed.

(* A simple traversal will find the maximum list element, which is a good upper
 * bound. *)
Definition listMax := fold_right max 0.

(* ...and we can prove it! *)
Theorem listMax_upperBound : forall init ls,
  forall n, In n ls -> fold_right max init ls >= n.
Proof.
  induct ls; simplify; propositional.
  linear_arithmetic.
  apply IHls in H0.
  linear_arithmetic.
Qed.

(* Now we restate that result as a computation refinement. *)
Theorem listMax_refines : forall ls,
  refine (pick upper where forall n, In n ls -> upper >= n) (ret (listMax ls)).
Proof.
  unfold refine, pick_, ret; simplify; subst.
  apply listMax_upperBound; assumption.
Qed.

(* An easy way to find a number higher than another: add 1! *)
Theorem increment_refines : forall n,
  refine (pick higher where higher > n) (ret (n + 1)).
Proof.
  unfold refine, pick_, ret; simplify; subst.
  linear_arithmetic.
Qed.

Ltac begin :=
  eexists; simplify;
    (* We run this next step to hide an evar, so that rewriting isn't too eager to
     * make up values for it. *)
    match goal with
    | [ |- refine _ (?f _) ] => set f
    end.

Ltac finish :=
  match goal with
  | [ |- refine ?e (?f ?arg) ] =>
    let g := eval pattern arg in e in
    match g with
    | ?g' _ =>
      let f' := eval unfold f in f in
      unify f' g'; reflexivity
    end
  end.

(* Let's derive an efficient implementation. *)
Theorem implementation : { f : list nat -> comp nat | forall ls, refine (notInList ls) (f ls) }.
Proof.
  begin.
  rewrite notInList_decompose.
  rewrite listMax_refines.
  setoid_rewrite increment_refines.
  (* ^-- Different tactic here to let us rewrite under a binder! *)
  rewrite bind_ret.
  finish.
Defined.

(* We can extract the program that we found as a standlone, executable Gallina
 * term. *)
Definition impl := Eval simpl in proj1_sig implementation.
Print impl.

(* We'll temporarily expose the definition of [max], so we can compute neatly
 * here. *)
Transparent max.
Eval compute in impl (1 :: 7 :: 8 :: 2 :: 13 :: 6 :: nil).
