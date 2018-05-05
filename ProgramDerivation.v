(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 16: Deriving Programs from Specifications
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/
  * Some material borrowed from Fiat <http://plv.csail.mit.edu/fiat/> *)

Require Import FrapWithoutSets.
Require Import Program Setoids.Setoid Classes.RelationClasses Classes.Morphisms Morphisms_Prop.
Require Import Eqdep.

Ltac inv_pair :=
  match goal with
  | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; invert H
  end.


(** * The computation monad *)

Definition comp (A : Type) := A -> Prop.

Definition ret {A} (x : A) : comp A := eq x.
Definition bind {A B} (c1 : comp A) (c2 : A -> comp B) : comp B :=
  fun b => exists a, c1 a /\ c2 a b.
Definition pick_ {A} (P : A -> Prop) : comp A := P.

Definition refine {A} (c1 c2 : comp A) :=
  forall a, c2 a -> c1 a.

Ltac morphisms := unfold refine, impl, pointwise_relation, bind, ret, pick_; hnf; first_order; subst; eauto.

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

Theorem pick_one : forall {A} {P : A -> Prop} v,
    P v
    -> refine (pick_ P) (ret v).
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

(* We run this next step to hide an evar, so that rewriting isn't too eager to
 * make up values for it. *)
Ltac hide_evars :=
  match goal with
  | [ |- refine _ (?f _ _) ] => set f
  | [ |- refine _ (?f _) ] => set f
  | [ |- refine _ ?f ] => set f
  end.

Ltac begin :=
  eexists; simplify; hide_evars.

Ltac finish :=
  match goal with
  | [ |- refine ?e (?f ?arg1 ?arg2) ] =>
    let g := eval pattern arg1, arg2 in e in
    match g with
    | ?g' _ _ =>
      let f' := eval unfold f in f in
      unify f' g'; reflexivity
    end
  | [ |- refine ?e (?f ?arg) ] =>
    let g := eval pattern arg in e in
    match g with
    | ?g' _ =>
      let f' := eval unfold f in f in
      unify f' g'; reflexivity
    end
  | [ |- refine ?e ?f ] =>
    let f' := eval unfold f in f in
    unify f' e; reflexivity
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

Hint Constructors RefineMethods.

Record adt_refine {names} (adt1 adt2 : adt names) : Prop := {
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
    RefineMethods eq ms ms.
Proof.
  induct ms.
  constructor.
  cases m; constructor; first_order.
  subst; eauto.
Qed.  

Hint Immediate RefineMethods_refl.

Theorem refine_refl : forall names (adt1 : adt names),
    adt_refine adt1 adt1.
Proof.
  simplify.
  choose_relation (@eq (AdtState adt1)); eauto.
Qed.

Lemma RefineMethods_trans : forall state1 state2 state3 names
                                   R1 R2
                                   (ms1 : methods state1 names)
                                   (ms2 : methods state2 names)
                                   (ms3 : methods state3 names),

    RefineMethods R1 ms1 ms2
    -> RefineMethods R2 ms2 ms3
    -> RefineMethods (fun s1 s3 => exists s2, R1 s1 s2 /\ R2 s2 s3) ms1 ms3.
Proof.
  induct 1; invert 1; repeat inv_pair; eauto.

  econstructor; eauto.
  first_order.
  eapply H5 in H2; eauto.
  first_order.
  eapply H in H2; eauto.
  first_order.
Qed.

Hint Resolve RefineMethods_trans.

Theorem refine_trans : forall names (adt1 adt2 adt3 : adt names),
    adt_refine adt1 adt2
    -> adt_refine adt2 adt3
    -> adt_refine adt1 adt3.
Proof.
  simplify.
  invert H.
  invert H0.
  choose_relation (fun s1 s3 => exists s2, ArRel s1 s2 /\ ArRel0 s2 s3); eauto.

  apply ArConstructors0 in H.
  first_order.
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
  choose_relation (@eq state); eauto.
Qed.

Inductive ReplaceMethod {state} (name : string)
          (oldbody newbody : state -> nat -> comp (state * nat))
  : forall {names}, methods state names -> methods state names -> Prop :=
| RepmHead : forall names (ms : methods state names),
    ReplaceMethod name oldbody newbody
                  (MethodsCons {| MethodName := name; MethodBody := oldbody |} ms)
                  (MethodsCons {| MethodName := name; MethodBody := newbody |} ms)
| RepmSkip : forall name' names oldbody' (ms1 ms2 : methods state names),
    name' <> name
    -> ReplaceMethod name oldbody newbody ms1 ms2
    -> ReplaceMethod name oldbody newbody
                  (MethodsCons {| MethodName := name'; MethodBody := oldbody' |} ms1)
                  (MethodsCons {| MethodName := name'; MethodBody := oldbody' |} ms2).

Theorem ReplaceMethod_ok : forall state name
                                  (oldbody newbody : state -> nat -> comp (state * nat))
                                  names (ms1 ms2 : methods state names),
    (forall s arg, refine (oldbody s arg) (newbody s arg))
    -> ReplaceMethod name oldbody newbody ms1 ms2
    -> RefineMethods eq ms1 ms2.
Proof.
  induct 1.

  econstructor; eauto.
  unfold refine in *; simplify; subst; eauto.

  econstructor; eauto.
  simplify; subst; eauto.
Qed.

Hint Resolve ReplaceMethod_ok.

Theorem refine_method : forall state name (oldbody newbody : state -> nat -> comp (state * nat))
                               names (ms1 ms2 : methods state names) constr,
    (forall s arg, refine (oldbody s arg) (newbody s arg))
    -> ReplaceMethod name oldbody newbody ms1 ms2
    -> adt_refine {| AdtState := state;
                     AdtConstructor := constr;
                     AdtMethods := ms1 |}
                  {| AdtState := state;
                     AdtConstructor := constr;
                     AdtMethods := ms2 |}.
Proof.
  simplify.
  choose_relation (@eq state); eauto.
Qed.

Inductive RepChangeMethods {state1 state2} (absfunc : state2 -> state1)
  : forall {names}, methods state1 names -> methods state2 names -> Prop :=
| RchNil :
    RepChangeMethods absfunc MethodsNil MethodsNil
| RchCons : forall name names oldbody (ms1 : methods state1 names) (ms2 : methods state2 names),
    RepChangeMethods absfunc ms1 ms2
    -> RepChangeMethods absfunc
       (MethodsCons {| MethodName := name; MethodBody := oldbody |} ms1)
       (MethodsCons {| MethodName := name; MethodBody := (fun s arg =>
                         p <- oldbody (absfunc s) arg;
                         s' <- pick s' where absfunc s' = fst p;
                         ret (s', snd p)) |} ms2).

Lemma RepChangeMethods_ok : forall state1 state2 (absfunc : state2 -> state1)
  names (ms1 : methods state1 names) (ms2 : methods state2 names),
    RepChangeMethods absfunc ms1 ms2
    -> RefineMethods (fun s1 s2 => absfunc s2 = s1) ms1 ms2.
Proof.
  induct 1; eauto.
  econstructor; eauto.
  morphisms.
  invert H3.
  cases x; simplify; subst.
  eauto.
Qed.

Hint Resolve RepChangeMethods_ok.

Theorem refine_rep : forall state1 state2 (absfunc : state2 -> state1)
                            names (ms1 : methods state1 names) (ms2 : methods state2 names)
                            constr,
    RepChangeMethods absfunc ms1 ms2
    -> adt_refine {| AdtState := state1;
                     AdtConstructor := constr;
                     AdtMethods := ms1 |}
                  {| AdtState := state2;
                     AdtConstructor := s0 <- constr; pick s where absfunc s = s0;
                     AdtMethods := ms2 |}.
Proof.
  simplify.
  choose_relation (fun s1 s2 => absfunc s2 = s1); eauto.
Qed.

(** ** Tactics for easy use of those refinement principles *)

Ltac refine_rep f := eapply refine_trans; [ apply refine_rep with (absfunc := f);
                                            repeat (apply RchNil
                                                    || refine (RchCons _ _ _ _ _ _ _)) | cbv beta ].

Ltac refine_constructor := eapply refine_trans; [ apply refine_constructor; hide_evars | ].

Ltac refine_method nam := eapply refine_trans; [ eapply refine_method with (name := nam); [
  | repeat (refine (RepmHead _ _ _ _ _)
            || (refine (RepmSkip _ _ _ _ _ _ _ _ _ _); [ equality | ])) ];
    cbv beta; simplify; hide_evars | ].

Ltac refine_finish := apply refine_refl.

(** ** Example: the numeric counter again *)

Definition derived_counter : { counter' | adt_refine counter counter' }.
  unfold counter; eexists.
  refine_rep (fun p => fst p + snd p).

  refine_constructor.
  rewrite bind_ret.
  rewrite (pick_one (0, 0)).
  finish.
  equality.

  refine_method "increment1".
  rewrite bind_ret; simplify.
  rewrite (pick_one (fst s + arg, snd s)).
  rewrite bind_ret; simplify.
  finish.
  simplify; linear_arithmetic.

  refine_method "increment2".
  rewrite bind_ret; simplify.
  rewrite (pick_one (fst s, snd s + arg)).
  rewrite bind_ret; simplify.
  finish.
  simplify; linear_arithmetic.

  refine_method "value".
  rewrite bind_ret; simplify.
  rewrite (pick_one s).
  rewrite bind_ret; simplify.
  finish.
  equality.

  refine_finish.
Defined.
  
Eval simpl in proj1_sig derived_counter.


(** * Another refinement strategy: introducing a cache (a.k.a. finite differencing) *)

Inductive CachingMethods {state} (name : string) (func : state -> nat)
  : forall {names}, methods state names -> methods (state * nat) names -> Prop :=
| CmNil :
    CachingMethods name func MethodsNil MethodsNil
| CmCached : forall names (ms1 : methods state names) (ms2 : methods _ names),
    CachingMethods name func ms1 ms2
    -> CachingMethods name func
       (MethodsCons {| MethodName := name; MethodBody := (fun s _ => ret (s, func s)) |} ms1)
       (MethodsCons {| MethodName := name; MethodBody := (fun s arg => ret (s, snd s)) |} ms2)
| CmDefault : forall name' names oldbody (ms1 : methods state names) (ms2 : methods _ names),
    name' <> name
    -> CachingMethods name func ms1 ms2
    -> CachingMethods name func
       (MethodsCons {| MethodName := name'; MethodBody := oldbody |} ms1)
       (MethodsCons {| MethodName := name'; MethodBody := (fun s arg =>
                         p <- oldbody (fst s) arg;
                         new_cache <- pick c where (func (fst s) = snd s -> func (fst p) = c);
                         ret ((fst p, new_cache), snd p)) |} ms2).

Lemma CachingMethods_ok  : forall state name (func : state -> nat)
                                  names (ms1 : methods state names) (ms2 : methods (state * nat) names),
    CachingMethods name func ms1 ms2
    -> RefineMethods (fun s1 s2 => fst s2 = s1 /\ snd s2 = func s1) ms1 ms2.
Proof.
  induct 1; eauto.

  econstructor; eauto.
  unfold ret, bind.
  simplify; first_order; subst.
  invert H1.
  rewrite H2.
  eauto.

  econstructor; eauto.
  unfold ret, bind.
  simplify; first_order; subst.
  invert H5.
  unfold pick_ in H4.
  cases x; simplify.
  eauto.
Qed.

Hint Resolve CachingMethods_ok.

Theorem refine_cache : forall state name (func : state -> nat)
                            names (ms1 : methods state names) (ms2 : methods (state * nat) names)
                            constr,
    CachingMethods name func ms1 ms2
    -> adt_refine {| AdtState := state;
                     AdtConstructor := constr;
                     AdtMethods := ms1 |}
                  {| AdtState := state * nat;
                     AdtConstructor := s0 <- constr; ret (s0, func s0);
                     AdtMethods := ms2 |}.
Proof.
  simplify.
  choose_relation (fun s1 s2 => fst s2 = s1 /\ snd s2 = func s1); eauto.

  unfold bind, ret in *.
  first_order; subst.
  simplify; eauto.
Qed.

Ltac refine_cache nam := eapply refine_trans; [ eapply refine_cache with (name := nam);
   repeat (apply CmNil
           || refine (CmCached _ _ _ _ _ _)
           || (refine (CmDefault _ _ _ _ _ _ _ _ _); [ equality | ])) | ].

(** ** An example with lists of numbers *)

Definition sum := fold_right plus 0.

Definition nats := ADT {
  rep = list nat
  and constructor = ret []
  and method "add"[[self, n]] = ret (n :: self, 0)
  and method "sum"[[self, _]] = ret (self, sum self)
}.

Definition optimized_nats : { nats' | adt_refine nats nats' }.
  unfold nats; eexists.

  refine_cache "sum".

  refine_constructor.
  rewrite bind_ret.
  finish.

  refine_method "add".
  rewrite bind_ret; simplify.
  rewrite (pick_one (arg + snd s)).
  rewrite bind_ret.
  finish.
  equality.

  refine_finish.
Defined.

Eval simpl in proj1_sig optimized_nats.
