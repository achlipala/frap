(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 11: Types and Mutation
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

(* Our approach to type soundness works beyond purely functional programs, too.
 * Let's see how it applies to a classic ML feature: mutable references.
 * We'll complete the full exercise for one semantics first, then go back and
 * extend the result to cover a semantics with another crucial real-world
 * feature. *)

Module References.
  Notation loc := nat.
  (* Locations are the values allowed for references.  Think of them as memory
   * addresses. *)

  Inductive exp : Set :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)

  | New (e1 : exp)
  (* Allocate a fresh reference, initialized with this value. *)

  | Read (e1 : exp)
  (* Return the value stored at this address. *)

  | Write (e1 e2 : exp)
  (* Overwrite the value at address [e1] with new value [e2]. *)

  | Loc (l : loc).
  (* A twist: though source programs may not mention locations directly,
   * intermediate execution states will need to include location constants. *)

  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1)

  | VLoc : forall l, value (Loc l).
  (* Locations are values, too. *)

  Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
    match e2 with
      | Var y => if y ==v x then e1 else Var y
      | Const n => Const n
      | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
      | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
      | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')

      | New e2' => New (subst e1 x e2')
      | Read e2' => Read (subst e1 x e2')
      | Write e2' e2'' => Write (subst e1 x e2') (subst e1 x e2'')
      | Loc l => Loc l
    end.

  (* We extend evaluation contexts in the natural way, though we won't dwell on
   * the details. *)

  Inductive context : Set :=
  | Hole : context
  | Plus1 : context -> exp -> context
  | Plus2 : exp -> context -> context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context
  | New1 : context -> context
  | Read1 : context -> context
  | Write1 : context -> exp -> context
  | Write2 : exp -> context -> context.

  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugPlus1 : forall e e' C e2,
    plug C e e'
    -> plug (Plus1 C e2) e (Plus e' e2)
  | PlugPlus2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Plus2 v1 C) e (Plus v1 e')
  | PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')

  | PlugNew1 : forall e e' C,
    plug C e e'
    -> plug (New1 C) e (New e')
  | PlugRead1 : forall e e' C,
    plug C e e'
    -> plug (Read1 C) e (Read e')
  | PlugWrite1 : forall e e' C e2,
    plug C e e'
    -> plug (Write1 C e2) e (Write e' e2)
  | PlugWrite2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Write2 v1 C) e (Write v1 e').

  Definition heap := fmap loc exp.
  (* A heap assigns a value to each allocated location. *)

  Inductive step0 : heap * exp -> heap * exp -> Prop :=
  | Beta : forall h x e v,
    value v
    -> step0 (h, App (Abs x e) v) (h, subst v x e)
  | Add : forall h n1 n2,
    step0 (h, Plus (Const n1) (Const n2)) (h, Const (n1 + n2))

  (* To run a [New], pick a location [l] that isn't used yet and stash the
   * requested value at that spot before returning it. *)
  | Allocate : forall h v l,
    value v
    -> h $? l = None
    -> step0 (h, New v) (h $+ (l, v), Loc l)

  (* To run a [Read], just look up in the heap. *)
  | Lookup : forall h v l,
    h $? l = Some v
    -> step0 (h, Read (Loc l)) (h, v)

  (* To run a [Write], just replace in the heap, *after* verifying that the
   * location is really present in the heap.  If not, this is another
   * opportunity to get stuck, which we will prove never occurs! *)
  | Overwrite : forall h v l v',
    value v'
    -> h $? l = Some v
    -> step0 (h, Write (Loc l) v') (h $+ (l, v'), v').

  (* The overall relation is much like before, with a heap added. *)
  Inductive step : heap * exp -> heap * exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2' h h',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 (h, e1) (h', e2)
    -> step (h, e1') (h', e2').

  Definition trsys_of (e : exp) := {|
    Initial := {($0, e)};
    Step := step
  |}.


  Inductive type :=
  | Nat
  | Fun (dom ran : type)
  | Ref (t : type).
  (* Crucial type addition: reference types *)

  (* New first parameter to typing relation: a *heap typing*, partial map from
   * locations to types *)
  Inductive hasty : fmap loc type -> fmap var type -> exp -> type -> Prop :=
  | HtVar : forall H G x t,
    G $? x = Some t
    -> hasty H G (Var x) t
  | HtConst : forall H G n,
    hasty H G (Const n) Nat
  | HtPlus : forall H G e1 e2,
    hasty H G e1 Nat
    -> hasty H G e2 Nat
    -> hasty H G (Plus e1 e2) Nat
  | HtAbs : forall H G x e1 t1 t2,
    hasty H (G $+ (x, t1)) e1 t2
    -> hasty H G (Abs x e1) (Fun t1 t2)
  | HtApp : forall H G e1 e2 t1 t2,
    hasty H G e1 (Fun t1 t2)
    -> hasty H G e2 t1
    -> hasty H G (App e1 e2) t2

  | HtNew : forall H G e1 t1,
    hasty H G e1 t1
    -> hasty H G (New e1) (Ref t1)
  | HtRead : forall H G e1 t1,
    hasty H G e1 (Ref t1)
    -> hasty H G (Read e1) t1
  | HtWrite : forall H G e1 e2 t1,
    hasty H G e1 (Ref t1)
    -> hasty H G e2 t1
    -> hasty H G (Write e1 e2) t1
  | HtLoc : forall H G l t,
     H $? l = Some t
     -> hasty H G (Loc l) (Ref t).
  (* Notice that the heap typing is only used here, for locations! *)

  (* When are a heap and a heap typing compatible? *)
  Inductive heapty (ht : fmap loc type) (h : fmap loc exp) : Prop :=
  | Heapty : forall bound,
      (* Condition 1: when the heap typing assigns a type to a location, the
       * heap assigns a value of that type to that location. *)
      (forall l t,
          ht $? l = Some t
          -> exists e, h $? l = Some e
                       /\ hasty ht $0 e t)

      (* Condition 2: all addresses above some bound are unallocated in the
       * heap.  Without this condition, we could get stuck proving that progress
       * can be made from a [New] expression, if the heap could be infinite! *)
      -> (forall l, l >= bound
                    -> h $? l = None)

      -> heapty ht h.
                 
  Hint Constructors value plug step0 step hasty heapty : core.


  (* Perhaps surprisingly, this language admits well-typed, nonterminating
   * programs!  Here's an example. *)
  Definition let_ (x : var) (e1 e2 : exp) :=
    App (Abs x e2) e1.
  Example loopy :=
    let_ "r" (New (Abs "x" (Var "x")))
         (let_ "_" (Write (Var "r") (Abs "x" (App (Read (Var "r")) (Var "x"))))
               (App (Read (Var "r")) (Const 0))).

  Theorem loopy_hasty : hasty $0 $0 loopy Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Hint Resolve lookup_add_eq : core.

  Ltac loopy := propositional; subst; simplify;
    repeat match goal with
           | [ x : (_ * _)%type |- _ ] => cases x; simplify
           end;
    propositional; subst;
    repeat match goal with
           | [ H : ex _ |- _ ] => invert H; propositional; subst
           end;
    try match goal with
        | [ H : step _ _ |- _ ] => invert H
        end;
    repeat match goal with
           | [ H : plug _ _ _ |- _ ] => invert1 H
           | [ H : plug _ _ _ |- _ ] => invert H
           | [ H : step0 _ _ |- _ ] => invert1 H
           | [ H : value _ |- _ ] => invert1 H
           | [ H : ?X = Some _, H' : ?X = Some _ |- _ ] => rewrite H in H'; invert H'
           end; eauto 7.

  Theorem loopy_diverge : invariantFor (trsys_of loopy) (fun he => ~value (snd he)).
  Proof.
    (* We prove divergence (unreachability of a value) by strengthening to an
     * invariant that enumerates all reachable expressions.  It isn't quite a
     * finite set.  We need to quantify existentially over the location chosen
     * for "r". *)
    apply invariant_weaken with (invariant1 := fun he =>
      snd he = loopy
      \/ exists l,
        (fst he $? l = Some (Abs "x" (Var "x")))
        /\ (snd he = let_ "r" (Loc l)
                          (let_ "_" (Write (Var "r") (Abs "x" (App (Read (Var "r")) (Var "x"))))
                                (App (Read (Var "r")) (Const 0)))
            \/ snd he = let_ "_" (Write (Loc l) (Abs "x" (App (Read (Loc l)) (Var "x"))))
                             (App (Read (Loc l)) (Const 0)))
        \/ (fst he $? l = Some (Abs "x" (App (Read (Loc l)) (Var "x")))
            /\ (snd he = let_ "_" (Abs "x" (App (Read (Loc l)) (Var "x")))
                               (App (Read (Loc l)) (Const 0))
                \/ snd he = App (Read (Loc l)) (Const 0)
                \/ snd he = App (Abs "x" (App (Read (Loc l)) (Var "x"))) (Const 0)))).

    apply invariant_induction; simplify.

    loopy.
    loopy.
    loopy.
  Qed.


  (** * Type soundness *)

  Definition unstuck (he : heap * exp) := value (snd he)
    \/ (exists he', step he he').

  Ltac t0 := match goal with
             | [ H : ex _ |- _ ] => invert H
             | [ H : _ /\ _ |- _ ] => invert H
             | [ |- context[?x ==v ?y] ] => cases (x ==v y)
             | [ H : Some _ = Some _ |- _ ] => invert H

             | [ H : heapty _ _ |- _ ] => invert H
             | [ H : step _ _ |- _ ] => invert H
             | [ H : step0 _ _ |- _ ] => invert1 H
             | [ H : hasty _ _ ?e _, H' : value ?e |- _ ] => (invert H'; invert H); []
             | [ H : hasty _ _ _ _ |- _ ] => invert1 H
             | [ H : plug _ _ _ |- _ ] => invert1 H
             end; subst.

  Ltac t := simplify; propositional; repeat (t0; simplify); try equality; eauto 7.

  Hint Extern 2 (exists _ : _ * _, _) => eexists (_ $+ (_, _), _) : core.

  (* Progress is quite straightforward. *)
  Lemma progress : forall ht h, heapty ht h
    -> forall e t,
      hasty ht $0 e t
      -> value e
         \/ exists he', step (h, e) he'.
  Proof.
    induct 2; t.
    match goal with
    | [ H1 : _ = Some _, H2 : forall l : loc, _ |- _ ] => apply H2 in H1; t
    end.
    match goal with
    | [ H1 : _ = Some _, H2 : forall l : loc, _ |- _ ] => apply H2 in H1; t
    end.
  Qed.

  (* Now, a series of lemmas essentially copied from original type-soundness
   * proof. *)

  Lemma weakening_override : forall (G G' : fmap var type) x t,
    (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
    -> (forall x' t', G $+ (x, t) $? x' = Some t'
                      -> G' $+ (x, t) $? x' = Some t').
  Proof.
    simplify.
    cases (x ==v x'); simplify; eauto.
  Qed.

  Hint Resolve weakening_override : core.

  Lemma weakening : forall H G e t,
    hasty H G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
      -> hasty H G' e t.
  Proof.
    induct 1; t.
  Qed.

  Hint Resolve weakening : core.

  Lemma hasty_change : forall H G e t,
    hasty H G e t
    -> forall G', G' = G
      -> hasty H G' e t.
  Proof.
    t.
  Qed.

  Hint Resolve hasty_change : core.

  Lemma substitution : forall H G x t' e t e',
    hasty H (G $+ (x, t')) e t
    -> hasty H $0 e' t'
    -> hasty H G (subst e' x e) t.
  Proof.
    induct 1; t.
  Qed.

  Hint Resolve substitution : core.

  (* A new property: expanding the heap typing preserves typing. *)
  Lemma heap_weakening : forall H G e t,
    hasty H G e t
    -> forall H', (forall x t, H $? x = Some t -> H' $? x = Some t)
      -> hasty H' G e t.
  Proof.
    induct 1; t.
  Qed.

  Hint Resolve heap_weakening : core.

  (* A property about extending heap typings *)
  Lemma heap_override : forall H h k t t0 l,
    H $? k = Some t
    -> heapty H h
    -> h $? l = None
    -> H $+ (l, t0) $? k = Some t.
  Proof.
    invert 2; simplify.
    cases (l ==n k); simplify; eauto.
    apply H2 in H0; t.
  Qed.

  Hint Resolve heap_override : core.

  (* A higher-level property, stated via [heapty] *)
  Lemma heapty_extend : forall H h l t v,
      heapty H h
      -> hasty H $0 v t
      -> h $? l = None
      -> heapty (H $+ (l, t)) (h $+ (l, v)).
  Proof.
    t.
    exists (max (S l) bound); simplify.

    cases (l ==n l0); simplify.
    invert H0; eauto 6.
    apply H3 in H0; t.

    apply H4.
    linear_arithmetic.
  Qed.

  Hint Resolve heapty_extend : core.

  (* The old cases of preservation proceed as before, and we need to fiddle with
   * the heap in the new cases.  Note a crucial change to the theorem statement:
   * now we say that *for all* original heap typings, *there exists* a new heap
   * typing that has not *dropped* any locations. *)
  Lemma preservation0 : forall h1 e1 h2 e2,
    step0 (h1, e1) (h2, e2)
    -> forall H1 t, hasty H1 $0 e1 t
                    -> heapty H1 h1
                    -> exists H2, hasty H2 $0 e2 t
                                  /\ heapty H2 h2
                                  /\ (forall l t, H1 $? l = Some t
                                                  -> H2 $? l = Some t).
  Proof.
    invert 1; t.

    exists (H1 $+ (l, t1)).
    split.
    econstructor.
    simplify.
    auto.
    eauto 6.

    apply H3 in H9; t.
    rewrite H1 in H2.
    invert H2.
    eauto.

    assert (H1 $? l = Some t) by assumption.
    apply H2 in H9.
    invert H9; propositional.
    rewrite H5 in H6.
    invert H6.
    eexists; propositional.
    eauto.
    exists bound; propositional.
    cases (l ==n l0); simplify; eauto.
    subst.
    rewrite H0 in H; invert H.
    eauto.
    apply H4 in H0.
    cases (l ==n l0); simplify; equality.
    assumption.
  Qed.

  Hint Resolve preservation0 : core.

  (* This lemma gets more complicated, too, to accommodate heap typings. *)
  Lemma generalize_plug : forall H e1 C e1',
    plug C e1 e1'
    -> forall t, hasty H $0 e1' t
    -> exists t0, hasty H $0 e1 t0
                  /\ (forall e2 e2' H',
                         hasty H' $0 e2 t0
                         -> plug C e2 e2'
                         -> (forall l t, H $? l = Some t -> H' $? l = Some t)
                         -> hasty H' $0 e2' t).
  Proof.
    Ltac applyIn := match goal with
                    | [ H : forall x, _, H' : _ |- _ ] =>
                      apply H in H'; clear H; invert H'; propositional
                    end.

    induct 1; t; (try applyIn; eexists; t).
  Qed.

  (* For overall preservation, most of the action was in the last few lemmas. *)
  Lemma preservation : forall h1 e1 h2 e2,
    step (h1, e1) (h2, e2)
    -> forall H1 t, hasty H1 $0 e1 t
                   -> heapty H1 h1
                   -> exists H2, hasty H2 $0 e2 t
                                 /\ heapty H2 h2.
  Proof.
    invert 1; simplify.
    eapply generalize_plug in H; eauto.
    invert H; propositional.
    eapply preservation0 in H6; eauto.
    invert H6; propositional.
    eauto.
  Qed.

  Hint Resolve progress preservation : core.

  (* We'll need this fact for the base case of invariant induction. *)
  Lemma heapty_empty : heapty $0 $0.
  Proof.
    exists 0; t.
  Qed.

  Hint Resolve heapty_empty : core.

  (* Now there isn't much more to the proof of type safety.  The crucial overall
   * insight is a strengthened invariant that quantifies existentially over a
   * heap typing. *)
  Theorem safety : forall e t, hasty $0 $0 e t
    -> invariantFor (trsys_of e)
                    (fun he' => value (snd he')
                                \/ exists he'', step he' he'').
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun he' => exists H,
                                                   hasty H $0 (snd he') t
                                                   /\ heapty H (fst he')); eauto.
    apply invariant_induction; simplify.
    propositional.
    subst; simplify.
    eauto.
    invert H0.
    propositional.
    cases s; cases s'; simplify.
    eauto.

    invert 1.
    propositional.
    cases s.
    eauto.
  Qed.
End References.

(* That last operational semantics lets references pile up in the heap.  Their
 * storage space is never reclaimed, even if the program will never use them
 * again.  It turns out, however, that our type system remains safe, even when
 * we extend the operational semantics with explicit *garbage collection*! *)

Module GarbageCollection.
  Import References.
  (* We'll start from the definitions we just made, only adding a few new ones
   * and revising a few. *)

  (* First key ingredient: which location constants appear in an expression? *)
  Fixpoint freeLocs (e : exp) : set loc :=
    match e with
    | Var _ => {}
    | Const _ => {}
    | Plus e1 e2 => freeLocs e1 \cup freeLocs e2
    | Abs _ e1 => freeLocs e1
    | App e1 e2 => freeLocs e1 \cup freeLocs e2
    | New e1 => freeLocs e1
    | Read e1 => freeLocs e1
    | Write e1 e2 => freeLocs e1 \cup freeLocs e2
    | Loc l => {l}
    end.

  (* When is there a path from one location to another through the heap, via
   * following free locations in the values associated to addresses? *)
  Inductive reachableLoc (h : heap) : loc -> loc -> Prop :=
  | ReachSelf : forall l, reachableLoc h l l
  | ReachLookup : forall l e l' l'',
      h $? l = Some e
      -> l' \in freeLocs e
      -> reachableLoc h l' l''
      -> reachableLoc h l l''.

  (* When is there a path from an expression to a location? *)
  Inductive reachableLocFromExp (h : heap) : exp -> loc -> Prop :=
  | ReachFromExp : forall l e l',
      l \in freeLocs e
      -> reachableLoc h l l'
      -> reachableLocFromExp h e l'.

  Inductive step : heap * exp -> heap * exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2' h h',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 (h, e1) (h', e2)
    -> step (h, e1') (h', e2')

  (* New rule for the operational semantics!  Pick heap [h'] that is the result
   * of garbage collecting [h]. *)
  | StepGc : forall h h' e lDefinitelyGone,

    (* Fundamental condition: any *reachable* location in [h] has been preserved
     * precisely in [h']. *)
    (forall l e',
        reachableLocFromExp h e l
        -> h $? l = Some e'
        -> h' $? l = Some e')

    (* However, [h'] has not sprouted any new locations.  It only keeps some
     * subset of [h]'s locations. *)
    -> (forall l e',
           h' $? l = Some e'
           -> h $? l = Some e')

    (* Finally, we require that [h'] has dropped at least one location from [h].
     * Why?  If not, type safety follows trivially, because, from any starting
     * expression, we can run an infinite loop of no-op "garbage collection"! *)
    -> h $? lDefinitelyGone <> None
    -> h' $? lDefinitelyGone = None

    -> step (h, e) (h', e).

  Hint Constructors step : core.

  Definition trsys_of (e : exp) := {|
    Initial := {($0, e)};
    Step := step
  |}.


  (** * Type soundness *)

  Definition unstuck (he : heap * exp) := value (snd he)
    \/ (exists he', step he he').

  (* Progress is easy; we essentially reuse the old proof, since the original
   * [step] case is enough to cover all expressions. *)
  Lemma progress : forall ht h, heapty ht h
    -> forall e t,
      hasty ht $0 e t
      -> value e
         \/ exists he', step (h, e) he'.
  Proof.
    intros.
    eapply References.progress in H0; t.
  Qed.

  (* For preservation, we'll need a few more lemmas.  First, reachability is
   * preserved by moving to a "larger" expression that contains "at least as
   * many" free locations. *)
  Lemma reachableLocFromExp_trans : forall h e1 l e2,
      reachableLocFromExp h e1 l
      -> freeLocs e1 \subseteq freeLocs e2
      -> reachableLocFromExp h e2 l.
  Proof.
    invert 1; simplify.
    econstructor.
    sets; eauto.
    assumption.
  Qed.

  Hint Resolve reachableLocFromExp_trans : core.
  Hint Extern 1 (_ \in _) => simplify; solve [ sets ] : core.
  Hint Extern 1 (_ \subseteq _) => simplify; solve [ sets ] : core.
  Hint Constructors reachableLoc reachableLocFromExp : core.

  (* Typing is preserved by moving to a heap typing that only needs to preserve
   * the mappings for *reachable* locations. *)
  Lemma hasty_restrict : forall H h H' G e t,
      heapty H h
      -> hasty H G e t
      -> (forall l t, reachableLocFromExp h e l
                      -> H $? l = Some t
                      -> H' $? l = Some t)
      -> hasty H' G e t.
  Proof.
    induct 2; simplify; econstructor; eauto.
  Qed.

  (* The sandwich properties, for adding a new reachability step through the
   * heap, between two other chains of arbitrary length *)
  Lemma reachableLoc_sandwich : forall h l l' e l'',
    reachableLoc h l l'
    -> h $? l' = Some e
    -> reachableLocFromExp h e l''
    -> reachableLoc h l l''.
  Proof.
    induct 1; simplify; eauto.
    invert H0; eauto.
  Qed.

  Lemma reachableLocFromExp_sandwich : forall h e l e' l',
    reachableLocFromExp h e l
    -> h $? l = Some e'
    -> reachableLocFromExp h e' l'
    -> reachableLocFromExp h e l'.
  Proof.
    invert 1; simplify.
    econstructor; eauto.
    eapply reachableLoc_sandwich; eauto.
  Qed.

  (* Finally, we are ready for preservation. *)
  Lemma preservation : forall h1 e1 h2 e2,
    step (h1, e1) (h2, e2)
    -> forall H1 t, hasty H1 $0 e1 t
                   -> heapty H1 h1
                   -> exists H2, hasty H2 $0 e2 t
                                 /\ heapty H2 h2.
  Proof.
    invert 1; simplify.

    (* The case for the original [step] rule proceeds exactly the same way as
     * before. *)
    eapply generalize_plug in H; eauto 3.
    invert H; propositional.
    eapply preservation0 in H6; eauto 3.
    invert H6; propositional.
    eauto.

    (* The key insight for the garbage-collection rule: as the new heap typing
     * after collection, choose the *restriction* of the original heap typing to
     * just the *reachable* locations. *)
    exists (restrict (reachableLocFromExp h1 e2) H1).
    propositional.

    eapply hasty_restrict; eauto.
    simplify.
    invert H0.
    assert (H1 $? l = Some t0) by assumption.
    apply H8 in H0.
    invert H0; propositional.

    assert (heapty H1 h1) by assumption.
    invert H2.
    exists bound; simplify; propositional.
    assert (reachableLocFromExp h1 e2 l) by (eapply lookup_restrict_true_fwd; eassumption).
    simplify.
    apply H3 in H2.
    invert H2; propositional.
    apply H4 in H2; auto.
    eexists; propositional.
    eauto.
    eapply hasty_restrict.
    eauto.
    eauto.
    simplify.
    assert (H1 $? l0 = Some t1) by assumption.
    apply H3 in H13.
    invert H13; propositional.
    simplify.
    rewrite lookup_restrict_true; auto.
    eapply reachableLocFromExp_sandwich; eauto.

    cases (h2 $? l); eauto.
    apply H8 in H2.
    apply H5 in Heq.
    equality.
  Qed.

  Hint Resolve progress preservation : core.

  (* The safety proof itself is anticlimactic, looking the same as before. *)
  Theorem safety : forall e t, hasty $0 $0 e t
    -> invariantFor (trsys_of e)
                    (fun he' => value (snd he')
                                \/ exists he'', step he' he'').
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun he' => exists H,
                                                   hasty H $0 (snd he') t
                                                   /\ heapty H (fst he')); eauto.
    apply invariant_induction; simplify.
    propositional.
    subst; simplify.
    eauto.
    invert H0.
    propositional.
    cases s; cases s'; simplify.
    eauto.

    invert 1.
    propositional.
    cases s.
    eauto.
  Qed.
End GarbageCollection.
