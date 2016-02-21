(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 6: Operational Semantics
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.


(* OK, enough with defining transition relations manually.  Let's return to our
 * syntax of imperative programs from Chapter 3. *)

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd).
(* Important differences: we added [If] and switched [Repeat] to general
 * [While]. *)

(* Here are some notations for the language, which again we won't really
 * explain. *)
Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";" := Sequence (at level 76).
Notation "'when' e 'do' then_ 'else' else_ 'done'" := (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'do' body 'done'" := (While e%arith body) (at level 75).

(* Here's an adaptation of our factorial example from Chapter 3. *)
Example factorial :=
  "output" <- 1;
  while "input" do
    "output" <- "output" * "input";
    "input" <- "input" - 1
  done.

(* Recall our use of a recursive function to interpret expressions. *)
Definition valuation := fmap var nat.
Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

(* Our old trick of interpreters won't work for this new language, because of
 * the general "while" loops.  No such interpreter could terminate for all
 * programs.  Instead, we will use inductive predicates to explain program
 * meanings.  First, let's apply the most intuitive method, called
 * *big-step operational semantics*. *)
Inductive eval : valuation -> cmd -> valuation -> Prop :=
| EvalSkip : forall v,
  eval v Skip v
| EvalAssign : forall v x e,
  eval v (Assign x e) (v $+ (x, interp e v))
| EvalSeq : forall v c1 v1 c2 v2,
  eval v c1 v1
  -> eval v1 c2 v2
  -> eval v (Sequence c1 c2) v2
| EvalIfTrue : forall v e then_ else_ v',
  interp e v <> 0
  -> eval v then_ v'
  -> eval v (If e then_ else_) v'
| EvalIfFalse : forall v e then_ else_ v',
  interp e v = 0
  -> eval v else_ v'
  -> eval v (If e then_ else_) v'
| EvalWhileTrue : forall v e body v' v'',
  interp e v <> 0
  -> eval v body v'
  -> eval v' (While e body) v''
  -> eval v (While e body) v''
| EvalWhileFalse : forall v e body,
  interp e v = 0
  -> eval v (While e body) v.

(* Let's run the factorial program on a few inputs. *)
Theorem factorial_2 : exists v, eval ($0 $+ ("input", 2)) factorial v
                                /\ v $? "output" = Some 2.
Proof.
  eexists; propositional.

  econstructor.
  econstructor.
  econstructor.
  simplify.
  equality.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  simplify.
  equality.
  econstructor.
  econstructor.
  econstructor.
  apply EvalWhileFalse.
  (* Note that, for this step, we had to specify which rule to use, since
   * otherwise [econstructor] incorrectly guesses [EvalWhileTrue]. *)
  simplify.
  equality.
  
  simplify.
  equality.
Qed.

(* That was rather repetitive.  It's easy to automate. *)

Ltac eval1 :=
  apply EvalSkip || apply EvalAssign || eapply EvalSeq
  || (apply EvalIfTrue; [ simplify; equality | ])
  || (apply EvalIfFalse; [ simplify; equality | ])
  || (eapply EvalWhileTrue; [ simplify; equality | | ])
  || (apply EvalWhileFalse; [ simplify; equality ]).
Ltac evaluate := simplify; try equality; repeat eval1.

Theorem factorial_2_snazzy : exists v, eval ($0 $+ ("input", 2)) factorial v
                                       /\ v $? "output" = Some 2.
Proof.
  eexists; propositional.
  evaluate.
  evaluate.
Qed.

Theorem factorial_3 : exists v, eval ($0 $+ ("input", 3)) factorial v
                                /\ v $? "output" = Some 6.
Proof.
  eexists; propositional.
  evaluate.
  evaluate.
Qed.

(* Instead of chugging through these relatively slow individual executions,
 * let's prove once and for all that [factorial] is correct. *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * fact n'
  end.

Example factorial_loop :=
  while "input" do
    "output" <- "output" * "input";
    "input" <- "input" - 1
  done.

Lemma factorial_loop_correct : forall n v out, v $? "input" = Some n
  -> v $? "output" = Some out
  -> exists v', eval v factorial_loop v'
                /\ v' $? "output" = Some (fact n * out).
Proof.
  induct n; simplify.

  exists v; propositional.
  apply EvalWhileFalse.
  simplify.
  rewrite H.
  equality.
  rewrite H0.
  f_equal.
  ring.

  assert (exists v', eval (v $+ ("output", out * S n) $+ ("input", n)) factorial_loop v'
                     /\ v' $? "output" = Some (fact n * (out * S n))).
  apply IHn.
  simplify; equality.
  simplify; equality.
  first_order.
  eexists; propositional.
  econstructor.
  simplify.
  rewrite H.
  equality.
  econstructor.
  econstructor.
  econstructor.
  simplify.
  rewrite H, H0.
  replace (S n - 1) with n by linear_arithmetic.
  (* [replace e1 with e2 by tac]: replace occurrences of [e1] with [e2], proving
   *   [e2 = e1] with tactic [tac]. *)
  apply H1.
  rewrite H2.
  f_equal.
  ring.
Qed.

Theorem factorial_correct : forall n v, v $? "input" = Some n
  -> exists v', eval v factorial v'
                /\ v' $? "output" = Some (fact n).
Proof.
  simplify.
  assert (exists v', eval (v $+ ("output", 1)) factorial_loop v'
                     /\ v' $? "output" = Some (fact n * 1)).
  apply factorial_loop_correct.
  simplify; equality.
  simplify; equality.
  first_order.
  eexists; propositional.
  econstructor.
  econstructor.
  simplify.
  apply H0.
  rewrite H1.
  f_equal.
  ring.
Qed.
