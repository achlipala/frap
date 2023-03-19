(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 11: Lambda Calculus and Simple Type Soundness
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

(* The last few chapters have focused on small programming languages that are
 * representative of the essence of the imperative languages.  We now turn to
 * lambda-calculus, the usual representative of functional languages. *)

Module Ulc.
  (* Programs are expressions, which we evaluate algebraically, rather than
   * executing for side effects. *)
  Inductive exp : Set :=
  | Var (x : var)
  | Abs (x : var) (body : exp)
    (* A function that binds its argument to the given variable, evaluating the
     * body expression *)
  | App (e1 e2 : exp).
    (* Applying a function to an argument *)

  (* Key operation: within [e], changing every occurrence of variable [x] into
   * [rep].  IMPORTANT: we will only apply this operation in contexts where
   * [rep] is *closed*, meaning every [Var] refers to some enclosing [Abs], so
   * as to avoid *variable capture*.  See the book proper for a little more
   * discussion. *)
  Fixpoint subst (rep : exp) (x : var) (e : exp) : exp :=
    match e with
    | Var y => if y ==v x then rep else Var y
    | Abs y e1 => Abs y (if y ==v x then e1 else subst rep x e1)
    | App e1 e2 => App (subst rep x e1) (subst rep x e2)
    end.


  (** * Big-step semantics *)

  (* This is the most straightforward way to give semantics to lambda terms:
   * We evaluate any closed term into a value (that is, an [Abs]). *)
  Inductive eval : exp -> exp -> Prop :=
  | BigAbs : forall x e,
    eval (Abs x e) (Abs x e)
  | BigApp : forall e1 x e1' e2 v2 v,
    eval e1 (Abs x e1')
    -> eval e2 v2
    -> eval (subst v2 x e1') v
    -> eval (App e1 e2) v.

  (* Note that we omit a [Var] case, since variable terms can't be *closed*,
   * and therefore they aren't meaningful as top-level programs. *)

  (* Which terms are values, that is, final results of execution? *)
  Inductive value : exp -> Prop :=
  | Value : forall x e, value (Abs x e).
  (* We're cheating a bit here, *assuming* that the term is also closed. *)

  Local Hint Constructors eval value : core.

  (* Every value executes to itself. *)
  Theorem value_eval : forall v,
    value v
    -> eval v v.
  Proof.
    invert 1; eauto.
  Qed.

  Local Hint Resolve value_eval : core.

  (* Conversely, let's prove that [eval] only produces values. *)
  Theorem eval_value : forall e v,
    eval e v
    -> value v.
  Proof.
    induct 1; eauto.
  Qed.

  Local Hint Resolve eval_value : core.

  (* Some notations, to let us write more normal-looking lambda terms *)
  Coercion Var : var >-> exp.
  Notation "\ x , e" := (Abs x e) (at level 50).
  Infix "@" := App (at level 49, left associativity).

  (* Believe it or not, this is a Turing-complete language!  Here's an example
   * nonterminating program. *)
  Example omega := (\"x", "x" @ "x") @ (\"x", "x" @ "x").

  Theorem omega_no_eval : forall v, eval omega v -> False.
  Proof.
    induct 1.

    invert H.
    invert H0.
    simplify.
    apply IHeval3.
    trivial.
  Qed.


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


  (** * Small-step semantics *)

  (* We can also port to this setting our small-step semantics style. *)

  (* Function application (called "beta reduction") is the big rule here. *)
  Inductive step : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> step (App (Abs x e) v) (subst v x e)

  (* However, we also need bureaucractic rules for pushing evaluation inside
   * applications. *)
  | App1 : forall e1 e1' e2,
      step e1 e1'
      -> step (App e1 e2) (App e1' e2)
  | App2 : forall v e2 e2',
      value v
      -> step e2 e2'
      -> step (App v e2) (App v e2').
  (* Note how that last rule enforces a deterministic evaluation order!
   * We call it *call-by-value*. *)

  Local Hint Constructors step : core.

  (* Here we now go through a proof of equivalence between big- and small-step
   * semantics, though we won't spend any further commentary on it. *)

  Lemma step_eval' : forall e1 e2,
    step e1 e2
    -> forall v, eval e2 v
      -> eval e1 v.
  Proof.
    induct 1; simplify; eauto.

    invert H0.
    econstructor.
    apply IHstep.
    eassumption.
    eassumption.
    assumption.

    invert H1.
    econstructor.
    eassumption.
    apply IHstep.
    eassumption.
    assumption.
  Qed.

  Local Hint Resolve step_eval' : core.

  Theorem step_eval : forall e v,
    step^* e v
    -> value v
    -> eval e v.
  Proof.
    induct 1; eauto.
  Qed.

  Local Hint Resolve eval_value : core.

  Theorem step_app1 : forall e1 e1' e2,
    step^* e1 e1'
    -> step^* (App e1 e2) (App e1' e2).
  Proof.
    induct 1; eauto.
  Qed.

  Theorem step_app2 : forall e2 e2' v,
    value v
    -> step^* e2 e2'
    -> step^* (App v e2) (App v e2').
  Proof.
    induct 2; eauto.
  Qed.

  Theorem eval_step : forall e v,
    eval e v
    -> step^* e v.
  Proof.
    induct 1; eauto.

    eapply trc_trans.
    apply step_app1.
    eassumption.
    eapply trc_trans.
    eapply step_app2.
    constructor.
    eassumption.
    econstructor.
    constructor.
    eauto.
    assumption.
  Qed.
End Ulc.


(** * Now we turn to a variant of lambda calculus with static type-checking.
    * This variant is called *simply typed* lambda calculus, and *simple* has a
    * technical meaning, basically meaning "no polymorphism" in the sense of
    * example file Polymorphism.v from this book. *)
Module Stlc.
  (* We add expression forms for numeric constants and addition. *)
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

  (* Small-step, call-by-value evaluation *)

  Inductive step : exp -> exp -> Prop :=
  (* These rules show the real action of the semantics. *)
  | Beta : forall x e v,
      value v
      -> step (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
      step (Plus (Const n1) (Const n2)) (Const (n1 + n2))
  (* Then we have a bunch of bureaucratic, repetitive rules encoding evaluation
   * order.  See next lecture for how to streamline this part, but for now note
   * that the [value] premises below are crucial to enforce a single order of
   * evaluation. *)
  | App1 : forall e1 e1' e2,
      step e1 e1'
      -> step (App e1 e2) (App e1' e2)
  | App2 : forall v e2 e2',
      value v
      -> step e2 e2'
      -> step (App v e2) (App v e2')
  | Plus1 : forall e1 e1' e2,
      step e1 e1'
      -> step (Plus e1 e2) (Plus e1' e2)
  | Plus2 : forall v e2 e2',
      value v
      -> step e2 e2'
      -> step (Plus v e2) (Plus v e2').

  (* It's easy to wrap everything as a transition system. *)
  Definition trsys_of (e : exp) := {|
    Initial := {e};
    Step := step
  |}.


  (* That language is suitable to describe with a static *type system*.  Here's
   * our modest, but countably infinite, set of types. *)
  Inductive type :=
  | Nat                  (* Numbers *)
  | Fun (dom ran : type) (* Functions *).

  (* Our typing relation (also often called a "judgment") uses *typing contexts*
   * (not to be confused with evaluation contexts) to map free variables to
   * their types.  Free variables are those that don't refer to enclosing [Abs]
   * binders. *)
  Inductive has_ty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
    G $? x = Some t
    -> has_ty G (Var x) t
  | HtConst : forall G n,
    has_ty G (Const n) Nat
  | HtPlus : forall G e1 e2,
    has_ty G e1 Nat
    -> has_ty G e2 Nat
    -> has_ty G (Plus e1 e2) Nat
  | HtAbs : forall G x e1 t1 t2,
    has_ty (G $+ (x, t1)) e1 t2
    -> has_ty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
    has_ty G e1 (Fun t1 t2)
    -> has_ty G e2 t1
    -> has_ty G (App e1 e2) t2.

  Local Hint Constructors value step has_ty : core.

  (* Some notation to make it more pleasant to write programs *)
  Infix "-->" := Fun (at level 60, right associativity).
  Coercion Const : nat >-> exp.
  Infix "^+^" := Plus (at level 50).
  Coercion Var : var >-> exp.
  Notation "\ x , e" := (Abs x e) (at level 51).
  Infix "@" := App (at level 49, left associativity).

  (* Some examples of typed programs *)

  Example one_plus_one : has_ty $0 (1 ^+^ 1) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example add : has_ty $0 (\"n", \"m", "n" ^+^ "m") (Nat --> Nat --> Nat).
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example eleven : has_ty $0 ((\"n", \"m", "n" ^+^ "m") @ 7 @ 4) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.

  Example seven_the_long_way : has_ty $0 ((\"x", "x") @ (\"x", "x") @ 7) Nat.
  Proof.
    repeat (econstructor; simplify).
  Qed.


  (** * Let's prove type soundness first without much automation. *)

  (* What useful invariants could we prove about programs in this language?  How
   * about that, at every point, either they're finished executing or they can
   * take further steps?  For instance, a program that tried to add a function
   * to a number would not satisfy that condition, and we call it *stuck*.  We
   * want to prove that typed programs can never become stuck.  Here's a good
   * invariant to strive for. *)
  Definition unstuck e := value e
    \/ (exists e' : exp, step e e').

  (* Now we're ready for the first of the two key properties to establish that
   * invariant: well-typed programs are never stuck. *)
  Lemma progress : forall e t,
    has_ty $0 e t
    -> unstuck e.
  Proof.
    unfold unstuck; induct 1; simplify; try equality.

    left.
    constructor.

    propositional.

    right.
    (* Some automation is needed here to maintain compatibility with
     * name generation in different Coq versions. *)
    match goal with
    | [ H1 : value e1, H2 : has_ty $0 e1 _ |- _ ] => invert H1; invert H2
    end.
    match goal with
    | [ H1 : value e2, H2 : has_ty $0 e2 _ |- _ ] => invert H1; invert H2
    end.
    exists (Const (n + n0)).
    constructor.

    match goal with
    | [ H : exists x, _ |- _ ] => invert H
    end.
    right.
    exists (x ^+^ e2).
    constructor.
    assumption.

    match goal with
    | [ H : exists x, _ |- _ ] => invert H
    end.
    right.
    exists (e1 ^+^ x).
    apply Plus2.
    assumption.
    assumption.

    match goal with
    | [ H : exists x, _ |- _ ] => invert H
    end.
    right.
    exists (x ^+^ e2).
    constructor.
    assumption.

    left.
    constructor.

    propositional.

    right.
    match goal with
    | [ H1 : value e1, H2 : has_ty $0 e1 _ |- _ ] => invert H1; invert H2
    end.
    exists (subst e2 x e0).
    constructor.
    assumption.

    match goal with
    | [ H : exists x, _ |- _ ] => invert H
    end.
    right.
    exists (x @ e2).
    constructor.
    assumption.

    match goal with
    | [ H : exists x, _ |- _ ] => invert H
    end.
    right.
    exists (e1 @ x).
    constructor.
    assumption.
    assumption.

    match goal with
    | [ H : exists x, step e1 _ |- _ ] => invert H
    end.
    right.
    exists (App x e2).
    constructor.

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

  (* This lemma lets us transplant a typing derivation into a new context that
   * includes the old one. *)
  Lemma weakening : forall G e t,
    has_ty G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
      -> has_ty G' e t.
  Proof.
    induct 1; simplify.

    constructor.
    apply H0.
    assumption.

    constructor.

    constructor.
    apply IHhas_ty1.
    assumption.
    apply IHhas_ty2.
    assumption.

    constructor.
    apply IHhas_ty.
    apply weakening_override.
    assumption.

    econstructor.
    apply IHhas_ty1.
    assumption.
    apply IHhas_ty2.
    assumption.
  Qed.

  (* Replacing a variable with a properly typed term preserves typing. *)
  Lemma substitution : forall G x t' e t e',
    has_ty (G $+ (x, t')) e t
    -> has_ty $0 e' t'
    -> has_ty G (subst e' x e) t.
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
    eapply IHhas_ty1; equality.
    eapply IHhas_ty2; equality.

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
    eapply IHhas_ty.
    maps_equal.
    assumption.

    econstructor.
    eapply IHhas_ty1; equality.
    eapply IHhas_ty2; equality.
  Qed.

  (* OK, now we're almost done.  Full steps really do preserve typing! *)
  Lemma preservation : forall e1 e2,
    step e1 e2
    -> forall t, has_ty $0 e1 t
      -> has_ty $0 e2 t.
  Proof.
    induct 1; simplify.

    invert H0.
    invert H4.
    eapply substitution.
    eassumption.
    assumption.
    
    invert H.
    constructor.

    invert H0.
    econstructor.
    apply IHstep.
    eassumption.
    assumption.

    invert H1.
    econstructor.
    eassumption.
    apply IHstep.
    assumption.

    invert H0.
    constructor.
    apply IHstep.
    assumption.
    assumption.

    invert H1.
    constructor.
    assumption.
    apply IHstep.
    assumption.
  Qed.

  (* Now watch this!  Though this syntactic approach to type soundness is usually
   * presented from scratch as a proof technique, it turns out that the two key
   * properties, progress and preservation, are just instances of the same methods
   * we've been applying all along with invariants of transition systems! *)
  Theorem safety : forall e t, has_ty $0 e t
    -> invariantFor (trsys_of e) unstuck.
  Proof.
    simplify.

    (* Step 1: strengthen the invariant.  In particular, the typing relation is
     * exactly the right stronger invariant!  Our progress theorem proves the
     * required invariant inclusion. *)
    apply invariant_weaken with (invariant1 := fun e' => has_ty $0 e' t).

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


  (** * Let's do that again with more automation, whose details are beyond the
      * scope of the book. *)

  Ltac t0 := match goal with
             | [ H : ex _ |- _ ] => invert H
             | [ H : _ /\ _ |- _ ] => invert H
             | [ |- context[?x ==v ?y] ] => cases (x ==v y)
             | [ H : Some _ = Some _ |- _ ] => invert H

             | [ H : step _ _ |- _ ] => invert1 H
             | [ H : has_ty _ ?e _, H' : value ?e |- _ ] => invert H'; invert H
             | [ H : has_ty _ _ _ |- _ ] => invert1 H
             end; subst.

  Ltac t := simplify; propositional; repeat (t0; simplify); try equality; eauto 6.

  Lemma progress_snazzy : forall e t,
    has_ty $0 e t
    -> value e
    \/ (exists e' : exp, step e e').
  Proof.
    induct 1; t.
  Qed.

  Local Hint Resolve weakening_override : core.

  Lemma weakening_snazzy : forall G e t,
    has_ty G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
      -> has_ty G' e t.
  Proof.
    induct 1; t.
  Qed.

  Local Hint Resolve weakening_snazzy : core.

  (* Replacing a typing context with an equal one has no effect (useful to guide
   * proof search as a hint). *)
  Lemma has_ty_change : forall G e t,
    has_ty G e t
    -> forall G', G' = G
      -> has_ty G' e t.
  Proof.
    t.
  Qed.

  Local Hint Resolve has_ty_change : core.

  Lemma substitution_snazzy : forall G x t' e t e',
    has_ty (G $+ (x, t')) e t
    -> has_ty $0 e' t'
    -> has_ty G (subst e' x e) t.
  Proof.
    induct 1; t.
  Qed.

  Local Hint Resolve substitution_snazzy : core.

  Lemma preservation_snazzy : forall e1 e2,
    step e1 e2
    -> forall t, has_ty $0 e1 t
      -> has_ty $0 e2 t.
  Proof.
    induct 1; t.
  Qed.

  Local Hint Resolve progress_snazzy preservation_snazzy : core.

  Theorem safety_snazzy : forall e t, has_ty $0 e t
    -> invariantFor (trsys_of e)
                    (fun e' => value e'
                               \/ exists e'', step e' e'').
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun e' => has_ty $0 e' t); eauto.
    apply invariant_induction; simplify; eauto; equality.
  Qed.
End Stlc.
