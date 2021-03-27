(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 12: More on Evaluation Contexts
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.


Module Stlc.
  Inductive exp : Set :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp).

  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1).

  Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
    match e2 with
      | Var y => if y ==v x then e1 else Var y
      | Const n => Const n
      | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
      | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
      | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
    end.

  Inductive context : Set :=
  | Hole : context
  | Plus1 : context -> exp -> context
  | Plus2 : exp -> context -> context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context.

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
    -> plug (App2 v1 C) e (App v1 e').

  (* Small-step, call-by-value evaluation, using our evaluation contexts *)

  (* First: the primitive reductions *)
  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
    step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2)).

  (* Then: running them in context *)
  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

  (* It's easy to wrap everything as a transition system. *)
  Definition trsys_of (e : exp) := {|
    Initial := {e};
    Step := step
  |}.


  (* Typing details are the same as last chapter. *)
  Inductive type :=
  | Nat                  (* Numbers *)
  | Fun (dom ran : type) (* Functions *).

  Inductive hasty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
    G $? x = Some t
    -> hasty G (Var x) t
  | HtConst : forall G n,
    hasty G (Const n) Nat
  | HtPlus : forall G e1 e2,
    hasty G e1 Nat
    -> hasty G e2 Nat
    -> hasty G (Plus e1 e2) Nat
  | HtAbs : forall G x e1 t1 t2,
    hasty (G $+ (x, t1)) e1 t2
    -> hasty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
    hasty G e1 (Fun t1 t2)
    -> hasty G e2 t1
    -> hasty G (App e1 e2) t2.

  Local Hint Constructors value plug step0 step hasty : core.

  Infix "-->" := Fun (at level 60, right associativity).
  Coercion Const : nat >-> exp.
  Infix "^+^" := Plus (at level 50).
  Coercion Var : var >-> exp.
  Notation "\ x , e" := (Abs x e) (at level 51).
  Infix "@" := App (at level 49, left associativity).

  (** * Now we adapt the automated proof of type soundness. *)

  Ltac t0 := match goal with
             | [ H : ex _ |- _ ] => invert H
             | [ H : _ /\ _ |- _ ] => invert H
             | [ |- context[?x ==v ?y] ] => cases (x ==v y)
             | [ H : Some _ = Some _ |- _ ] => invert H

             | [ H : step _ _ |- _ ] => invert H
             | [ H : step0 _ _ |- _ ] => invert1 H
             | [ H : hasty _ ?e _, H' : value ?e |- _ ] => invert H'; invert H
             | [ H : hasty _ _ _ |- _ ] => invert1 H
             | [ H : plug _ _ _ |- _ ] => invert1 H
             end; subst.

  Ltac t := simplify; propositional; repeat (t0; simplify); try equality; eauto 6.

  Lemma progress : forall e t,
    hasty $0 e t
    -> value e
    \/ (exists e' : exp, step e e').
  Proof.
    induct 1; t.
  Qed.

  Lemma weakening_override : forall (G G' : fmap var type) x t,
    (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
    -> (forall x' t', G $+ (x, t) $? x' = Some t'
                      -> G' $+ (x, t) $? x' = Some t').
  Proof.
    simplify.
    cases (x ==v x'); simplify; eauto.
  Qed.

  Local Hint Resolve weakening_override : core.

  Lemma weakening : forall G e t,
    hasty G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
      -> hasty G' e t.
  Proof.
    induct 1; t.
  Qed.

  Local Hint Resolve weakening : core.

  (* Replacing a typing context with an equal one has no effect (useful to guide
   * proof search as a hint). *)
  Lemma hasty_change : forall G e t,
    hasty G e t
    -> forall G', G' = G
      -> hasty G' e t.
  Proof.
    t.
  Qed.

  Local Hint Resolve hasty_change : core.

  Lemma substitution : forall G x t' e t e',
    hasty (G $+ (x, t')) e t
    -> hasty $0 e' t'
    -> hasty G (subst e' x e) t.
  Proof.
    induct 1; t.
  Qed.

  Local Hint Resolve substitution : core.

  Lemma preservation0 : forall e1 e2,
    step0 e1 e2
    -> forall t, hasty $0 e1 t
      -> hasty $0 e2 t.
  Proof.
    invert 1; t.
  Qed.

  Local Hint Resolve preservation0 : core.

  Lemma preservation' : forall C e1 e1',
      plug C e1 e1'
      -> forall e2 e2' t, plug C e2 e2'
      -> step0 e1 e2
      -> hasty $0 e1' t
      -> hasty $0 e2' t.
  Proof.
    induct 1; t.
  Qed.

  Local Hint Resolve preservation' : core.
  
  Lemma preservation : forall e1 e2,
    step e1 e2
    -> forall t, hasty $0 e1 t
      -> hasty $0 e2 t.
  Proof.
    invert 1; t.
  Qed.

  Local Hint Resolve progress preservation : core.

  Theorem safety : forall e t, hasty $0 e t
    -> invariantFor (trsys_of e)
                    (fun e' => value e'
                               \/ exists e'', step e' e'').
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun e' => hasty $0 e' t); eauto.
    apply invariant_induction; simplify; eauto; equality.
  Qed.
End Stlc.
