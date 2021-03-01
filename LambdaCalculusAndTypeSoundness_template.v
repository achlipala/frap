(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 11: Lambda Calculus and Simple Type Soundness
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

(* The last few chapters have focused on small programming languages that are
 * representative of the essence of the imperative languages.  We now turn to
 * lambda-calculus, the usual representative of functional languages. *)

Module Ulc.
  Inductive exp : Set :=
  | Var (x : var)
  | Abs (x : var) (body : exp)
  | App (e1 e2 : exp).

  Fixpoint subst (rep : exp) (x : var) (e : exp) : exp :=
    match e with
    | Var y => if y ==v x then rep else Var y
    | Abs y e1 => Abs y (if y ==v x then e1 else subst rep x e1)
    | App e1 e2 => App (subst rep x e1) (subst rep x e2)
    end.


  (** * Big-step semantics *)

  Inductive eval : exp -> exp -> Prop :=
  | BigAbs : forall x e,
    eval (Abs x e) (Abs x e)
  | BigApp : forall e1 x e1' e2 v2 v,
    eval e1 (Abs x e1')
    -> eval e2 v2
    -> eval (subst v2 x e1') v
    -> eval (App e1 e2) v.

  Inductive value : exp -> Prop :=
  | Value : forall x e, value (Abs x e).

  Hint Constructors eval value.

  Theorem value_eval : forall v,
    value v
    -> eval v v.
  Proof.
    invert 1; eauto.
  Qed.

  Hint Resolve value_eval.

  Theorem eval_value : forall e v,
    eval e v
    -> value v.
  Proof.
    induct 1; eauto.
  Qed.

  Hint Resolve eval_value.

  (* Some notations, to let us write more normal-looking lambda terms *)
  Coercion Var : var >-> exp.
  Notation "\ x , e" := (Abs x e) (at level 50).
  Infix "@" := App (at level 49, left associativity).

  (* Believe it or not, this is a Turing-complete language!  Here's an example
   * nonterminating program. *)
  Example omega := (\"x", "x" @ "x") @ (\"x", "x" @ "x").


  (** * Church Numerals, everyone's favorite example of lambda terms in
      * action *)

  (* Here are two curious definitions. *)
  Definition zero := \"f", \"x", "x".
  Definition plus1 := \"n", \"f", \"x", "f" @ ("n" @ "f" @ "x").

  (* We can build up any natural number [n] as [plus1^n @ zero].  Let's prove
   * that, in fact, these definitions constitute a workable embedding of the
   * natural numbers in lambda-calculus. *)

  (* A term [plus^n @ zero] evaluates to something very close to what this
   * function returns. *)
  Fixpoint canonical' (n : nat) : exp :=
    match n with
    | O => "x"
    | S n' => "f" @ ((\"f", \"x", canonical' n') @ "f" @ "x")
    end.

  (* This missing piece is this wrapper. *)
  Definition canonical n := \"f", \"x", canonical' n.

  (* Let's formalize our definition of what it means to represent a number. *)
  Definition represents (e : exp) (n : nat) :=
    eval e (canonical n).

  (* Zero passes the test. *)
  Theorem zero_ok : represents zero 0.
  Proof.
    unfold zero, represents, canonical.
    simplify.
    econstructor.
  Qed.

  (* So does our successor operation. *)
  Theorem plus1_ok : forall e n, represents e n
                                 -> represents (plus1 @ e) (S n).
  Proof.
    unfold plus1, represents, canonical; simplify.
    econstructor.
    econstructor.
    eassumption.
    simplify.
    econstructor.
  Qed.

  (* What's basically going on here?  The representation of number [n] is [N]
   * such that, for any function [f]:
   *   N(f) = f^n
   * That is, we represent a number as its repeated-composition operator.
   * So, given a number, we can use it to repeat any operation.  In particular,
   * to implement addition, we can just repeat [plus1]! *)
  Definition add := \"n", \"m", "n" @ plus1 @ "m".

  (* Our addition works properly on this test case. *)
  Example add_1_2 : exists v,
      eval (add @ (plus1 @ zero) @ (plus1 @ (plus1 @ zero))) v
      /\ eval (plus1 @ (plus1 @ (plus1 @ zero))) v.
  Proof.
    eexists; propositional.
    repeat (econstructor; simplify).
    repeat econstructor.
  Qed.

  (* By the way: since [canonical'] doesn't mention variable "m", substituting
   * for "m" has no effect.  This fact will come in handy shortly. *)
  Lemma subst_m_canonical' : forall m n,
    subst m "m" (canonical' n) = canonical' n.
  Proof.
    induct n; simplify; equality.
  Qed.

  (* This inductive proof is the workhorse for the next result, so let's skip
   * ahead there. *)
  Lemma add_ok' : forall m n,
      eval
        (subst (\ "f", (\ "x", canonical' m)) "x"
               (subst (\ "n", (\ "f", (\ "x", "f" @ (("n" @ "f") @ "x")))) "f"
                      (canonical' n))) (canonical (n + m)).
  Proof.
    induct n; simplify.

    econstructor.

    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simplify.
    econstructor.
    econstructor.
    simplify.
    eassumption.

    simplify.
    econstructor.
  Qed.

  (* [add] properly encodes the usual addition. *)
  Theorem add_ok : forall n ne m me,
      represents ne n
      -> represents me m
      -> represents (add @ ne @ me) (n + m).
  Proof.
    unfold represents; simplify.

    econstructor.
    econstructor.
    econstructor.
    eassumption.
    simplify.
    econstructor.
    eassumption.
    simplify.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simplify.
    econstructor.
    econstructor.
    rewrite subst_m_canonical'.
    apply add_ok'.
  Qed.

  (* Let's repeat the same exercise for multiplication. *)

  Definition mult := \"n", \"m", "n" @ (add @ "m") @ zero.

  Example mult_1_2 : exists v,
      eval (mult @ (plus1 @ zero) @ (plus1 @ (plus1 @ zero))) v
      /\ eval (plus1 @ (plus1 @ zero)) v.
  Proof.
    eexists; propositional.
    repeat (econstructor; simplify).
    repeat econstructor.
  Qed.

  Lemma mult_ok' : forall m n,
      eval
        (subst (\ "f", (\ "x", "x")) "x"
               (subst
                  (\ "m",
                   ((\ "f", (\ "x", canonical' m)) @
                                                   (\ "n", (\ "f", (\ "x", "f" @ (("n" @ "f") @ "x"))))) @ "m")
                  "f" (canonical' n))) (canonical (n * m)).
  Proof.
    induct n; simplify.

    econstructor.

    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simplify.
    econstructor.
    econstructor.
    simplify.
    eassumption.

    simplify.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simplify.
    econstructor.
    econstructor.
    rewrite subst_m_canonical'.
    apply add_ok'. (* Note the recursive appeal to correctness of [add]. *)
  Qed.

  Theorem mult_ok : forall n ne m me,
      represents ne n
      -> represents me m
      -> represents (mult @ ne @ me) (n * m).
  Proof.
    unfold represents; simplify.

    econstructor.
    econstructor.
    econstructor.
    eassumption.
    simplify.
    econstructor.
    eassumption.
    simplify.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simplify.
    econstructor.
    simplify.
    econstructor.
    econstructor.
    simplify.
    rewrite subst_m_canonical'.
    apply mult_ok'.
  Qed.


  (** * Small-step semantics with evaluation contexts *)

  Inductive context : Set :=
  | Hole : context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context.

  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e,
    plug Hole e e
  | PlugApp1 : forall c e1 e2 e,
    plug c e1 e
    -> plug (App1 c e2) e1 (App e e2)
  | PlugApp2 : forall c e1 e2 e,
    value e1
    -> plug c e2 e
    -> plug (App2 e1 c) e2 (App e1 e).

  Inductive step : exp -> exp -> Prop :=
  | ContextBeta : forall c x e v e1 e2,
    value v
    -> plug c (App (Abs x e) v) e1
    -> plug c (subst v x e) e2
    -> step e1 e2.

  Hint Constructors plug step.

  (* Here we now go through a proof of equivalence between big- and small-step
   * semantics, though we won't spend any further commentary on it. *)

  Lemma step_eval'' : forall v c x e e1 e2 v0,
    value v
    -> plug c (App (Abs x e) v) e1
    -> plug c (subst v x e) e2
    -> eval e2 v0
    -> eval e1 v0.
  Proof.
    induct c; invert 2; invert 1; simplify; eauto.
    invert H0; eauto.
    invert H0; eauto.
  Qed.

  Hint Resolve step_eval''.

  Lemma step_eval' : forall e1 e2,
    step e1 e2
    -> forall v, eval e2 v
      -> eval e1 v.
  Proof.
    invert 1; simplify; eauto.
  Qed.

  Hint Resolve step_eval'.

  Theorem step_eval : forall e v,
    step^* e v
    -> value v
    -> eval e v.
  Proof.
    induct 1; eauto.
  Qed.

  Lemma plug_functional : forall C e e1,
      plug C e e1
      -> forall e2, plug C e e2
                    -> e1 = e2.
  Proof.
    induct 1; invert 1; simplify; try f_equal; eauto.
  Qed.

  Lemma plug_mirror : forall C e e', plug C e e'
    -> forall e1, exists e1', plug C e1 e1'.
  Proof.
    induct 1; simplify; eauto.

    specialize (IHplug e0); first_order; eauto.

    specialize (IHplug e0); first_order; eauto.
  Qed.    

  Fixpoint compose (C1 C2 : context) : context :=
    match C2 with
    | Hole => C1
    | App1 C2' e => App1 (compose C1 C2') e
    | App2 v C2' => App2 v (compose C1 C2')
    end.

  Lemma compose_ok : forall C1 C2 e1 e2 e3,
      plug C1 e1 e2
      -> plug C2 e2 e3
      -> plug (compose C1 C2) e1 e3.
  Proof.
    induct 2; simplify; eauto.
  Qed.

  Hint Resolve compose_ok.

  Lemma step_plug : forall e1 e2,
    step e1 e2
    -> forall C e1' e2', plug C e1 e1'
                         -> plug C e2 e2'
                         -> step e1' e2'.
  Proof.
    invert 1; simplify; eauto.
  Qed.

  Lemma stepStar_plug : forall e1 e2,
    step^* e1 e2
    -> forall C e1' e2', plug C e1 e1'
                         -> plug C e2 e2'
                         -> step^* e1' e2'.
  Proof.
    induct 1; simplify.

    assert (e1' = e2') by (eapply plug_functional; eassumption).
    subst.
    constructor.

    assert (exists y', plug C y y') by eauto using plug_mirror.
    invert H3.
    eapply step_plug in H.
    econstructor.
    eassumption.
    eapply IHtrc.
    eassumption.
    assumption.
    eassumption.
    assumption.
  Qed.

  Hint Resolve stepStar_plug eval_value.

  Theorem eval_step : forall e v,
    eval e v
    -> step^* e v.
  Proof.
    induct 1; eauto.

    eapply trc_trans.
    eapply stepStar_plug with (e1 := e1) (e2 := Abs x e1') (C := App1 Hole e2); eauto.
    eapply trc_trans.
    eapply stepStar_plug with (e1 := e2) (e2 := v2) (C := App2 (Abs x e1') Hole); eauto.
    eauto.
  Qed.
End Ulc.


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

  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
    step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2)).

  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

  Definition trsys_of (e : exp) := {|
    Initial := {e};
    Step := step
  |}.


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

  Hint Constructors value plug step0 step hasty.

  (* Some notation to make it more pleasant to write programs *)
  Infix "-->" := Fun (at level 60, right associativity).
  Coercion Const : nat >-> exp.
  Infix "^+^" := Plus (at level 50).
  Coercion Var : var >-> exp.
  Notation "\ x , e" := (Abs x e) (at level 51).
  Infix "@" := App (at level 49, left associativity).

  (* Some examples of typed programs *)

  Example one_plus_one : hasty $0 (1 ^+^ 1) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example add : hasty $0 (\"n", \"m", "n" ^+^ "m") (Nat --> Nat --> Nat).
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example eleven : hasty $0 ((\"n", \"m", "n" ^+^ "m") @ 7 @ 4) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example seven_the_long_way : hasty $0 ((\"x", "x") @ (\"x", "x") @ 7) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.


  (** * Let's prove type soundness. *)

  Definition unstuck e := value e
    \/ (exists e' : exp, step e e').

  Lemma progress : forall e t,
    hasty $0 e t
    -> value e
    \/ (exists e' : exp, step e e').
  Proof.
  Admitted.

  (* Replacing a typing context with an equal one has no effect (useful to guide
   * proof search as a hint). *)
  Lemma hasty_change : forall G e t,
    hasty G e t
    -> forall G', G' = G
      -> hasty G' e t.
  Proof.
  Admitted.

  Hint Resolve hasty_change.

  Lemma preservation : forall e1 e2,
    step e1 e2
    -> forall t, hasty $0 e1 t
      -> hasty $0 e2 t.
  Proof.
  Admitted.

  Theorem safety : forall e t, hasty $0 e t
    -> invariantFor (trsys_of e) unstuck.
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
End Stlc.
