(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 9: Types and Mutation
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Module Rlc.
  Notation loc := nat.

  Inductive exp : Set :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)

  | New (e1 : exp)
  | Read (e1 : exp)
  | Write (e1 e2 : exp)
  | Loc (l : loc).

  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1)

  | VLoc : forall l, value (Loc l).

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

  Inductive step0 : heap * exp -> heap * exp -> Prop :=
  | Beta : forall h x e v,
    value v
    -> step0 (h, App (Abs x e) v) (h, subst v x e)
  | Add : forall h n1 n2,
    step0 (h, Plus (Const n1) (Const n2)) (h, Const (n1 + n2))
  | Allocate : forall h v l,
    value v
    -> h $? l = None
    -> step0 (h, New v) (h $+ (l, v), Loc l)
  | Lookup : forall h v l,
    h $? l = Some v
    -> step0 (h, Read (Loc l)) (h, v)
  | Overwrite : forall h v l v',
    h $? l = Some v
    -> step0 (h, Write (Loc l) v') (h $+ (l, v'), v').

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

  Inductive heapty (ht : fmap loc type) (h : fmap loc exp) : Prop :=
  | Heapty : forall bound,
      (forall l t,
          ht $? l = Some t
          -> exists e, h $? l = Some e
                       /\ hasty ht $0 e t)
      -> (forall l, l >= bound
                    -> h $? l = None)
      -> heapty ht h.
                 
  Hint Constructors value plug step0 step hasty heapty.


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

             | [ H : forall l t, ?h $? l = Some t -> _,
                 H' : ?h $? _ = Some _ |- _ ] => apply H in H'
             end; subst.

  Ltac t := simplify; propositional; repeat (t0; simplify); try equality; eauto 7.

  Hint Extern 2 (exists _ : _ * _, _) => eexists (_ $+ (_, _), _).

  Lemma progress : forall ht h, heapty ht h
    -> forall e t,
      hasty ht $0 e t
      -> value e
         \/ exists he', step (h, e) he'.
  Proof.
    induct 2; t.
  Qed.

  Lemma weakening_override : forall (G G' : fmap var type) x t,
    (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
    -> (forall x' t', G $+ (x, t) $? x' = Some t'
                      -> G' $+ (x, t) $? x' = Some t').
  Proof.
    simplify.
    cases (x ==v x'); simplify; eauto.
  Qed.

  Hint Resolve weakening_override.

  Lemma weakening : forall H G e t,
    hasty H G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
      -> hasty H G' e t.
  Proof.
    induct 1; t.
  Qed.

  Hint Resolve weakening.

  Lemma hasty_change : forall H G e t,
    hasty H G e t
    -> forall G', G' = G
      -> hasty H G' e t.
  Proof.
    t.
  Qed.

  Hint Resolve hasty_change.

  Lemma substitution : forall H G x t' e t e',
    hasty H (G $+ (x, t')) e t
    -> hasty H $0 e' t'
    -> hasty H G (subst e' x e) t.
  Proof.
    induct 1; t.
  Qed.

  Hint Resolve substitution.

  Lemma heap_weakening : forall H G e t,
    hasty H G e t
    -> forall H', (forall x t, H $? x = Some t -> H' $? x = Some t)
      -> hasty H' G e t.
  Proof.
    induct 1; t.
  Qed.

  Hint Resolve heap_weakening.

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

  Hint Resolve heap_override.

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

    rewrite lookup_add_ne by linear_arithmetic.
    apply H4.
    linear_arithmetic.
  Qed.

  Hint Resolve heapty_extend.

  Lemma preservation0 : forall h1 e1 h2 e2,
    step0 (h1, e1) (h2, e2)
    -> forall H1 t, hasty H1 $0 e1 t
                    -> heapty H1 h1
                    -> exists H2, hasty H2 $0 e2 t
                                  /\ heapty H2 h2.
  Proof.
    invert 1; t.

    exists (H1 $+ (l, t1)).
    split.
    econstructor.
    simplify.
    auto.
    eauto.

    rewrite H1 in H2.
    invert H2.
    eauto.

    rewrite H1 in H2.
    invert H2.
    exists H0; propositional.
  Admitted.

  Hint Resolve preservation0.

  Lemma generalize_plug : forall e1 C e1',
    plug C e1 e1'
    -> forall e2 e2', plug C e2 e2'
      -> (forall H t, hasty H $0 e1 t -> hasty H $0 e2 t)
      -> (forall H t, hasty H $0 e1' t -> hasty H $0 e2' t).
  Proof.
    induct 1; t.
  Qed.

  Hint Resolve generalize_plug.

  Lemma preservation : forall h1 e1 h2 e2,
    step (h1, e1) (h2, e2)
    -> forall H1 t, hasty H1 $0 e1 t
                   -> heapty H1 h1
                   -> exists H2, hasty H2 $0 e2 t
                                 /\ heapty H2 h2.
  Proof.
    invert 1; simplify.
    eapply preservation0 in H6.
    invert H6; propositional.
    exists x; propositional.
    3: eauto.
  Admitted.

  Hint Resolve progress preservation.

  Lemma heapty_empty : heapty $0 $0.
  Proof.
    exists 0; t.
  Qed.

  Hint Resolve heapty_empty.

  Theorem safety : forall e t, hasty $0 $0 e t
    -> invariantFor (trsys_of e)
                    (fun he' => value (snd he')
                                \/ exists he'', step he' he'').
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun he' => exists H,
                                                   hasty H $0 (snd he') t
                                                   /\ heapty H (fst he')); eauto.
    apply invariant_induction; simplify; eauto.
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
End Rlc.
