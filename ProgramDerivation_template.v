Require Import Frap.
Require Import Program Setoids.Setoid Classes.RelationClasses Classes.Morphisms Morphisms_Prop.
Require Import Eqdep.

Set Warnings "-cannot-define-projection".

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

(** ** OK, back to the details we want to focus on. *)

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


(** * Some handy tactics *)

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


(** * Picking a number not in a list *)

Definition notInList (ls : list nat) :=
  pick n where ~In n ls.

Definition implementation : sig (fun f : list nat -> comp nat => forall ls, refine (notInList ls) (f ls)).
Admitted.

(*Definition impl := Eval simpl in proj1_sig implementation.

Transparent max.
Eval compute in impl (1 :: 7 :: 8 :: 2 :: 13 :: 6 :: nil).*)


(** * Abstract data types (ADTs) *)

Record method_ {state : Type} := {
  MethodName : string;
  MethodBody : state -> nat -> comp (state * nat)
}.
Arguments method_ : clear implicits.

Notation "'method' name [[ self , arg ]] = body" :=
  {| MethodName := name;
     MethodBody := fun self arg => body |}
    (at level 100, self at level 0, arg at level 0).

Inductive methods {state : Type} : list string -> Type :=
| MethodsNil : methods []
| MethodsCons : forall (m : method_ state) {names},
    methods names
    -> methods (MethodName m :: names).

Arguments methods : clear implicits.

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

Definition counter := ADT {
  rep = nat
  and constructor = ret 0
  and method "increment1"[[self, arg]] = ret (self + arg, 0)
  and method "increment2"[[self, arg]] = ret (self + arg, 0)
  and method "value"[[self, _]] = ret (self, self)
}.


(** * ADT refinement *)

Inductive RefineMethods {state1 state2} (R : state1 -> state2 -> Prop)
  : forall {names}, methods state1 names -> methods state2 names -> Prop :=
| RmNil : RefineMethods R MethodsNil MethodsNil
| RmCons : forall name names (f1 : state1 -> nat -> comp (state1 * nat))
                  (f2 : state2 -> nat -> comp (state2 * nat))
                  (ms1 : methods state1 names) (ms2 : methods state2 names),

    (* This condition is the classic "simulation diagram." *)
    (forall s1 s2 arg s2' res,
        R s1 s2
        -> f2 s2 arg (s2', res)
        -> exists s1', f1 s1 arg (s1', res)
                       /\ R s1' s2')

    -> RefineMethods R ms1 ms2
    -> RefineMethods R (MethodsCons {| MethodName := name; MethodBody := f1 |} ms1)
                       (MethodsCons {| MethodName := name; MethodBody := f2 |} ms2).

Local Hint Constructors RefineMethods : core.

Record adt_refine {names} (adt1 adt2 : adt names) : Prop := {
  ArRel : AdtState adt1 -> AdtState adt2 -> Prop;
  ArConstructors : forall s2,
      AdtConstructor adt2 s2
      -> exists s1, AdtConstructor adt1 s1
                    /\ ArRel s1 s2;
  ArMethods : RefineMethods ArRel (AdtMethods adt1) (AdtMethods adt2)
}.

(* We will use this handy tactic to prove ADT refinements. *)
Ltac choose_relation R :=
  match goal with
  | [ |- adt_refine ?a ?b ] => apply (Build_adt_refine _ a b R)
  end; simplify.

(** ** Example: numeric counter *)

Definition split_counter := ADT {
  rep = nat * nat
  and constructor = ret (0, 0)
  and method "increment1"[[self, arg]] = ret ((fst self + arg, snd self), 0)
  and method "increment2"[[self, arg]] = ret ((fst self, snd self + arg), 0)
  and method "value"[[self, _]] = ret (self, fst self + snd self)
}.

Local Hint Extern 1 (@eq nat _ _) => simplify; linear_arithmetic : core.

Theorem split_counter_ok : adt_refine counter split_counter.
Proof.
Admitted.


(** * General refinement strategies *)

Lemma RefineMethods_refl : forall state names (ms : methods state names),
    RefineMethods eq ms ms.
Proof.
  induct ms.
  constructor.
  cases m; constructor; first_order.
  subst; eauto.
Qed.  

Local Hint Immediate RefineMethods_refl : core.

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

Local Hint Resolve RefineMethods_trans : core.

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

(** ** Refining constructors *)

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

(** ** Refining methods *)

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

Lemma ReplaceMethod_ok : forall state name
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

Local Hint Resolve ReplaceMethod_ok : core.

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

(** ** Representation changes *)

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

Local Hint Resolve RepChangeMethods_ok : core.

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

Definition derived_counter : sig (adt_refine counter).
Admitted.

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
       (MethodsCons {| MethodName := name; MethodBody := (fun s _ => ret (s, snd s)) |} ms2)
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

Local Hint Resolve CachingMethods_ok : core.

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

Definition optimized_nats : sig (adt_refine nats).
Admitted.

Eval simpl in proj1_sig optimized_nats.
