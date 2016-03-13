(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 8: Lambda Calculus and Simple Type Soundness
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

(* Expression syntax *)
Inductive exp : Set :=
| Var (x : var)
| Const (n : nat)
| Plus (e1 e2 : exp)
| Abs (x : var) (e1 : exp)
| App (e1 e2 : exp).

(* Values (final results of evaluation) *)
Inductive value : exp -> Prop :=
| VConst : forall n, value (Const n)
| VAbs : forall x e1, value (Abs x e1).

(* Substitution (not applicable when [e1] isn't closed, to avoid some complexity
 * that we don't need) *)
Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
  match e2 with
    | Var y => if y ==v x then e1 else Var y
    | Const n => Const n
    | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
    | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
    | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
  end.

(* Evaluation contexts *)
Inductive context : Set :=
| Hole : context
| Plus1 : context -> exp -> context
| Plus2 : exp -> context -> context
| App1 : context -> exp -> context
| App2 : exp -> context -> context.

(* Plugging an expression into a context *)
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


(* Syntax of types *)
Inductive type : Set :=
| Nat
| Fun (dom ran : type).

(* Our typing judgment uses *typing contexts* (not to be confused with
 * evaluation contexts) to map free variables to their types. *)
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

Hint Constructors value plug step0 step hasty.


(** * Let's prove type soundness first without much automation. *)

(* Now we're ready for the first of the two key properties, to show that "has
 * type t in the empty typing context" is an invariant. *)
Lemma progress : forall e t,
  hasty $0 e t
  -> value e
  \/ (exists e' : exp, step e e').
Proof.
  induct 1; simplify; try equality.

  left.
  constructor.

  propositional.

  right.
  invert H1; invert H.
  invert H2; invert H0.
  exists (Const (n + n0)).
  eapply StepRule with (C := Hole).
  eauto.
  eauto.
  constructor.

  invert H2.
  right.
  invert H3.
  exists (Plus e1 x).
  eapply StepRule with (C := Plus2 e1 C).
  eauto.
  eauto.
  assumption.

  invert H1.
  invert H3.
  right.
  exists (Plus x e2).
  eapply StepRule with (C := Plus1 C e2).
  eauto.
  eauto.
  assumption.

  invert H1.
  invert H3.
  right.
  exists (Plus x e2).
  eapply StepRule with (C := Plus1 C e2).
  eauto.
  eauto.
  assumption.

  left.
  constructor.

  propositional.
  
  right.
  invert H1; invert H.
  exists (subst e2 x e0).
  eapply StepRule with (C := Hole).
  eauto.
  eauto.
  constructor.
  assumption.

  invert H2.
  right.
  invert H3.
  exists (App e1 x).
  eapply StepRule with (C := App2 e1 C).
  eauto.
  eauto.
  assumption.

  invert H1.
  invert H3.
  right.
  exists (App x e2).
  eapply StepRule with (C := App1 C e2).
  eauto.
  eauto.
  assumption.

  invert H1.
  invert H3.
  right.
  exists (App x e2).
  eapply StepRule with (C := App1 C e2).
  eauto.
  eauto.
  assumption.
Qed.

(* Inclusion between typing contexts is preserved by adding the same new mapping
 * to both. *)
Lemma weakening_override : forall (G G' : fmap var type) x t,
  (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
  -> (forall x' t', G $+ (x, t) $? x' = Some t'
                    -> G' $+ (x, t) $? x' = Some t').
Proof.
  simplify.
  cases (x ==v x'); simplify; eauto.
Qed.

(** Raising a typing derivation to a larger typing context *)
Lemma weakening : forall G e t,
  hasty G e t
  -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
    -> hasty G' e t.
Proof.
  induct 1; simplify.

  constructor.
  apply H0.
  assumption.

  constructor.

  constructor.
  apply IHhasty1.
  assumption.
  apply IHhasty2.
  assumption.

  constructor.
  apply IHhasty.
  apply weakening_override.
  assumption.

  econstructor.
  apply IHhasty1.
  assumption.
  apply IHhasty2.
  assumption.
Qed.

(* Replacing a variable with a properly typed term preserves typing. *)
Lemma substitution : forall G x t' e t e',
  hasty (G $+ (x, t')) e t
  -> hasty $0 e' t'
  -> hasty G (subst e' x e) t.
Proof.
  induct 1; simplify.

  cases (x0 ==v x).

  simplify.
  invert H.
  eapply weakening.
  eassumption.
  simplify.
  equality.

  simplify.
  constructor.
  assumption.

  constructor.

  constructor.
  apply IHhasty1.
  assumption.
  apply IHhasty2.
  assumption.

  cases (x0 ==v x).

  constructor.
  eapply weakening.
  eassumption.
  simplify.
  cases (x0 ==v x1).

  simplify.
  assumption.

  simplify.
  assumption.

  constructor.
  eapply IHhasty.
  maps_equal.
  assumption.

  econstructor.
  apply IHhasty1.
  assumption.
  apply IHhasty2.
  assumption.
Qed.

(* We're almost ready for the main preservation property.  Let's prove it first
 * for the more basic [step0] relation. *)
Lemma preservation0 : forall e1 e2,
  step0 e1 e2
  -> forall t, hasty $0 e1 t
    -> hasty $0 e2 t.
Proof.
  invert 1; simplify.

  invert H.
  invert H4.
  eapply substitution.
  eassumption.
  assumption.
  
  invert H.
  constructor.
Qed.

(* We also need this key property, essentially saying that, if [e1] and [e2] are
 * "type-equivalent," then they remain "type-equivalent" after wrapping the same
 * context around both. *)
Lemma generalize_plug : forall e1 C e1',
  plug C e1 e1'
  -> forall e2 e2', plug C e2 e2'
    -> (forall t, hasty $0 e1 t -> hasty $0 e2 t)
    -> (forall t, hasty $0 e1' t -> hasty $0 e2' t).
Proof.
  induct 1; simplify.

  invert H.
  apply H0.
  assumption.

  invert H0.
  invert H2.
  constructor.
  eapply IHplug.
  eassumption.
  assumption.
  assumption.
  assumption.

  invert H1.
  invert H3.
  constructor.
  assumption.
  eapply IHplug.
  eassumption.
  assumption.
  assumption.

  invert H0.
  invert H2.
  econstructor.
  eapply IHplug.
  eassumption.
  assumption.
  eassumption.
  assumption.

  invert H1.
  invert H3.
  econstructor.
  eassumption.
  eapply IHplug.
  eassumption.
  assumption.
  eassumption.
Qed.

(* OK, now we're almost done. *)
Lemma preservation : forall e1 e2,
  step e1 e2
  -> forall t, hasty $0 e1 t
    -> hasty $0 e2 t.
Proof.
  invert 1; simplify.

  eapply generalize_plug with (e1' := e1).
  eassumption.
  eassumption.
  simplify.
  eapply preservation0.
  eassumption.
  assumption.
  assumption.
Qed.

(* Now watch this!  Though the syntactic approach to type soundness is usually
 * presented from scratch as a proof technique, it turns out that the two key
 * properties, progress and preservation, are just instances of the same methods
 * we've been applying all along with invariants of transition systems! *)
Theorem safety : forall e t, hasty $0 e t
  -> invariantFor (trsys_of e)
                  (fun e' => value e'
                             \/ exists e'', step e' e'').
Proof.
  simplify.

  (* Step 1: strengthen the invariant.  In particular, the typing relation is
   * exactly the right stronger invariant!  Our progress theorem proves the
   * required invariant inclusion. *)
  apply invariant_weaken with (invariant1 := fun e' => hasty $0 e' t).

  (* Step 2: apply invariant induction, whose induction step turns out to match
   * our preservation theorem exactly! *)
  apply invariant_induction; simplify.
  equality.

  eapply preservation.
  eassumption.
  assumption.

  simplify.
  eapply progress.
  eassumption.
Qed.


(** * Let's do that again with more automation. *)

Ltac t0 := match goal with
           | [ H : ex _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ |- context[?x ==v ?y] ] => destruct (x ==v y)
           | [ H : Some _ = Some _ |- _ ] => invert H

           | [ H : step _ _ |- _ ] => invert H
           | [ H : step0 _ _ |- _ ] => invert1 H
           | [ H : hasty _ ?e _, H' : value ?e |- _ ] => invert H'; invert H
           | [ H : hasty _ _ _ |- _ ] => invert1 H
           | [ H : plug _ _ _ |- _ ] => invert1 H
           end; subst.

Ltac t := simplify; propositional; repeat (t0; simplify); try congruence; eauto 6.

Lemma progress_snazzy : forall e t,
  hasty $0 e t
  -> value e
  \/ (exists e' : exp, step e e').
Proof.
  induct 1; t.
Qed.

Hint Resolve weakening_override.

Lemma weakening_snazzy : forall G e t,
  hasty G e t
  -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
    -> hasty G' e t.
Proof.
  induct 1; t.
Qed.

Hint Resolve weakening_snazzy.

(* Replacing a typing context with an equal one has no effect (useful to guide
 * proof search). *)
Lemma hasty_change : forall G e t,
  hasty G e t
  -> forall G', G' = G
    -> hasty G' e t.
Proof.
  t.
Qed.

Hint Resolve hasty_change.

Lemma substitution_snazzy : forall G x t' e t e',
  hasty (G $+ (x, t')) e t
  -> hasty $0 e' t'
  -> hasty G (subst e' x e) t.
Proof.
  induct 1; t.
Qed.

Hint Resolve substitution_snazzy.

Lemma preservation0_snazzy : forall e1 e2,
  step0 e1 e2
  -> forall t, hasty $0 e1 t
    -> hasty $0 e2 t.
Proof.
  invert 1; t.
Qed.

Hint Resolve preservation0_snazzy.

Lemma generalize_plug_snazzy : forall e1 C e1',
  plug C e1 e1'
  -> forall e2 e2', plug C e2 e2'
    -> (forall t, hasty $0 e1 t -> hasty $0 e2 t)
    -> (forall t, hasty $0 e1' t -> hasty $0 e2' t).
Proof.
  induct 1; t.
Qed.

Hint Resolve generalize_plug_snazzy.

Lemma preservation_snazzy : forall e1 e2,
  step e1 e2
  -> forall t, hasty $0 e1 t
    -> hasty $0 e2 t.
Proof.
  invert 1; t.
Qed.

Hint Resolve progress_snazzy preservation_snazzy.

Theorem safety_snazzy : forall e t, hasty $0 e t
  -> invariantFor (trsys_of e)
                  (fun e' => value e'
                             \/ exists e'', step e' e'').
Proof.
  simplify.
  apply invariant_weaken with (invariant1 := fun e' => hasty $0 e' t); eauto.
  apply invariant_induction; simplify; eauto; equality.
Qed.