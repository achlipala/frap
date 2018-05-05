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


(** * Abstract data types (ADTs) *)

Record method_ {state : Type} := {
  MethodName : string;
  MethodBody : state -> nat -> comp (state * nat)
}.

Arguments method_ : clear implicits.

Inductive methods {state : Type} : list string -> Type :=
| MethodsNil : methods []
| MethodsCons : forall (m : method_ state) {names},
    methods names
    -> methods (MethodName m :: names).

Arguments methods : clear implicits.

Notation "'method' name [[ self , arg ]] = body" :=
  {| MethodName := name;
     MethodBody := fun self arg => body |}
    (at level 100, self at level 0, arg at level 0).

Record adt {names : list string} := {
  AdtState : Type;
  AdtConstructor : comp AdtState;
  AdtMethods : methods AdtState names
}.

Arguments adt : clear implicits.

Notation "'ADT' { 'rep' = state 'and' 'constructor' = constr ms }" :=
  {| AdtState := state;
     AdtConstructor := constr;
     AdtMethods := ms |}.

Notation "'and' m1 'and' .. 'and' mn" :=
  (MethodsCons m1 (.. (MethodsCons mn MethodsNil) ..)) (at level 101).


(** * ADT refinement *)

Inductive RefineMethods {state1 state2} (R : state1 -> state2 -> Prop)
  : forall {names}, methods state1 names -> methods state2 names -> Prop :=
| RmNil : RefineMethods R MethodsNil MethodsNil
| RmCons : forall name names (f1 : state1 -> nat -> comp (state1 * nat))
                  (f2 : state2 -> nat -> comp (state2 * nat))
                  (ms1 : methods state1 names) (ms2 : methods state2 names),
    (forall s1 s2 arg s2' res,
        R s1 s2
        -> f2 s2 arg (s2', res)
        -> exists s1', f1 s1 arg (s1', res)
                       /\ R s1' s2')
    -> RefineMethods R ms1 ms2
    -> RefineMethods R (MethodsCons {| MethodName := name; MethodBody := f1 |} ms1)
                       (MethodsCons {| MethodName := name; MethodBody := f2 |} ms2).

Record adt_refine {names} (adt1 adt2 : adt names) := {
  ArRel : AdtState adt1 -> AdtState adt2 -> Prop;
  ArConstructors : forall s2,
      AdtConstructor adt2 s2
      -> exists s1, AdtConstructor adt1 s1
                    /\ ArRel s1 s2;
  ArMethods : RefineMethods ArRel (AdtMethods adt1) (AdtMethods adt2)
}.

Ltac choose_relation R :=
  match goal with
  | [ |- adt_refine ?a ?b ] => apply (Build_adt_refine _ a b R)
  end; simplify.

(** ** Example: numeric counter *)

Definition counter := ADT {
  rep = nat
  and constructor = ret 0
  and method "increment1"[[self, arg]] = ret (self + arg, 0)
  and method "increment2"[[self, arg]] = ret (self + arg, 0)
  and method "value"[[self, _]] = ret (self, self)
}.

Definition split_counter := ADT {
  rep = nat * nat
  and constructor = ret (0, 0)
  and method "increment1"[[self, arg]] = ret ((fst self + arg, snd self), 0)
  and method "increment2"[[self, arg]] = ret ((fst self, snd self + arg), 0)
  and method "value"[[self, _]] = ret (self, fst self + snd self)
}.

Hint Extern 1 (@eq nat _ _) => simplify; linear_arithmetic.

Theorem split_counter_ok : adt_refine counter split_counter.
Proof.
  choose_relation (fun n p => n = fst p + snd p).

  unfold ret in *; subst.
  eauto.

  repeat constructor; simplify; unfold ret in *; subst;
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => invert H
    end; eauto.

  Grab Existential Variables.
  exact 0.
Qed.


(** * General refinement strategies *)

Lemma RefineMethods_refl : forall state names (ms : methods state names),
    RefineMethods (@eq _) ms ms.
Proof.
  induct ms.
  constructor.
  cases m; constructor; first_order.
  subst; eauto.
Qed.  

Theorem refine_constructor : forall names state constr1 constr2 (ms : methods _ names),
    refine constr1 constr2
    -> adt_refine {| AdtState := state;
                     AdtConstructor := constr1;
                     AdtMethods := ms |}
                  {| AdtState := state;
                     AdtConstructor := constr2;
                     AdtMethods := ms |}.
Proof.
  simplify.
  match goal with
  | [ |- adt_refine ?a ?b ] => apply (Build_adt_refine names a b (@eq _))
  end; simplify.
  morphisms.
  apply RefineMethods_refl.
Qed.
