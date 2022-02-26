(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 8: Operational Semantics
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
Infix ";;" := Sequence (at level 76). (* This one changed slightly, to avoid parsing clashes. *)
Notation "'when' e 'then' then_ 'else' else_ 'done'" := (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (While e%arith body) (at level 75).

(* Here's an adaptation of our factorial example from Chapter 3. *)
Example factorial :=
  "output" <- 1;;
  while "input" loop
    "output" <- "output" * "input";;
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
  (* [eexists]: to prove [exists x, P(x)], switch to proving [P(?y)], for a new
   *   existential variable [?y]. *)

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
  while "input" loop
    "output" <- "output" * "input";;
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


(** * Small-step semantics *)

(* Big-step semantics only tells us something about the behavior of terminating
 * programs.  Our imperative language clearly supports nontermination, thanks to
 * the inclusion of general "while" loops.  A switch to *small-step* semantics
 * lets us also explain what happens with nonterminating executions, and this
 * style will also come in handy for more advanced features like concurrency. *)

Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
| StepAssign : forall v x e,
  step (v, Assign x e) (v $+ (x, interp e v), Skip)
| StepSeq1 : forall v c1 c2 v' c1',
  step (v, c1) (v', c1')
  -> step (v, Sequence c1 c2) (v', Sequence c1' c2)
| StepSeq2 : forall v c2,
  step (v, Sequence Skip c2) (v, c2)
| StepIfTrue : forall v e then_ else_,
  interp e v <> 0
  -> step (v, If e then_ else_) (v, then_)
| StepIfFalse : forall v e then_ else_,
  interp e v = 0
  -> step (v, If e then_ else_) (v, else_)
| StepWhileTrue : forall v e body,
  interp e v <> 0
  -> step (v, While e body) (v, Sequence body (While e body))
| StepWhileFalse : forall v e body,
  interp e v = 0
  -> step (v, While e body) (v, Skip).

(* Here's a small-step factorial execution. *)
Theorem factorial_2_small : exists v, step^* ($0 $+ ("input", 2), factorial) (v, Skip)
                                      /\ v $? "output" = Some 2.
Proof.
  eexists; propositional.

  econstructor.
  econstructor.
  econstructor.
  econstructor.
  apply StepSeq2.
  econstructor.
  econstructor.
  simplify.
  equality.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  apply StepSeq2.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  apply StepSeq2.
  econstructor.
  econstructor.
  simplify.
  equality.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  apply StepSeq2.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  apply StepSeq2.
  econstructor.
  apply StepWhileFalse.
  simplify.
  equality.
  econstructor.
  
  simplify.
  equality.
Qed.

Ltac step1 :=
  apply TrcRefl || eapply TrcFront
  || apply StepAssign || apply StepSeq2 || eapply StepSeq1
  || (apply StepIfTrue; [ simplify; equality ])
  || (apply StepIfFalse; [ simplify; equality ])
  || (eapply StepWhileTrue; [ simplify; equality ])
  || (apply StepWhileFalse; [ simplify; equality ]).
Ltac stepper := simplify; try equality; repeat step1.

Theorem factorial_2_small_snazzy : exists v, step^* ($0 $+ ("input", 2), factorial) (v, Skip)
                                             /\ v $? "output" = Some 2.
Proof.
  eexists; propositional.

  stepper.
  stepper.
Qed.

(* It turns out that these two semantics styles are equivalent.  Let's prove
 * it. *)

(* Automated proofs used here, if only to save time in class.
 * See book code for more manual proofs, too. *)

Local Hint Constructors trc step eval : core.

Theorem big_small : forall v c v', eval v c v'
  -> step^* (v, c) (v', Skip).
Proof.
Admitted.

Theorem small_big : forall v c v', step^* (v, c) (v', Skip)
                                   -> eval v c v'.
Proof.
Admitted.

















(** * Small-step semantics gives rise to transition systems. *)

Definition trsys_of (v : valuation) (c : cmd) : trsys (valuation * cmd) := {|
  Initial := {(v, c)};
  Step := step
|}.

Theorem simple_invariant :
  invariantFor (trsys_of ($0 $+ ("a", 1)) ("b" <- "a" + 1;; "c" <- "b" + "b"))
               (fun s => snd s = Skip -> fst s $? "c" = Some 4).
Proof.
  model_check.
Qed.

Inductive isEven : nat -> Prop :=
| EvenO : isEven 0
| EvenSS : forall n, isEven n -> isEven (S (S n)).

Lemma isEven_minus2 : forall n, isEven n -> isEven (n - 2).
Proof.
  induct 1; simplify.

  constructor.

  replace (n - 0) with n by linear_arithmetic.
  assumption.
Qed.

Lemma isEven_plus : forall n m,
  isEven n
  -> isEven m
  -> isEven (n + m).
Proof.
  induct 1; simplify.

  assumption.

  constructor.
  apply IHisEven.
  assumption.
Qed.

Local Hint Constructors isEven : core.
Local Hint Resolve isEven_minus2 isEven_plus : core.

Definition my_loop :=
  while "n" loop
    "a" <- "a" + "n";;
    "n" <- "n" - 2
  done.

Theorem manually_proved_invariant : forall n,
  isEven n
  -> invariantFor (trsys_of ($0 $+ ("n", n) $+ ("a", 0)) (while "n" loop "a" <- "a" + "n";; "n" <- "n" - 2 done))
               (fun s => exists a, fst s $? "a" = Some a /\ isEven a).
Proof.
Admitted.


























Definition all_programs := {
  (while "n" loop
     "a" <- "a" + "n";;
     "n" <- "n" - 2
   done),
  ("a" <- "a" + "n";;
   "n" <- "n" - 2),
  (Skip;;
   "n" <- "n" - 2),
  ("n" <- "n" - 2),
  (("a" <- "a" + "n";;
    "n" <- "n" - 2);;
   while "n" loop
     "a" <- "a" + "n";;
     "n" <- "n" - 2
   done),
  ((Skip;;
    "n" <- "n" - 2);;
   while "n" loop
     "a" <- "a" + "n";;
     "n" <- "n" - 2
   done),
  ("n" <- "n" - 2;;
   while "n" loop
     "a" <- "a" + "n";;
     "n" <- "n" - 2
   done),
  (Skip;;
   while "n" loop
     "a" <- "a" + "n";;
     "n" <- "n" - 2
   done),
  Skip
}.

Lemma manually_proved_invariant' : forall n,
  isEven n
  -> invariantFor (trsys_of ($0 $+ ("n", n) $+ ("a", 0)) (while "n" loop "a" <- "a" + "n";; "n" <- "n" - 2 done))
               (fun s => all_programs (snd s)
                         /\ exists n a, fst s $? "n" = Some n
                                        /\ fst s $? "a" = Some a
                                        /\ isEven n
                                        /\ isEven a).
Proof.
  simplify; apply invariant_induction; simplify; unfold all_programs in *; first_order; subst; simplify;
  try match goal with
      | [ H : step _ _ |- _ ] => invert H; simplify
      end;
  repeat (match goal with
          | [ H : _ = Some _ |- _ ] => rewrite H
          | [ H : @eq cmd (_ _ _) _ |- _ ] => invert H
          | [ H : @eq cmd (_ _ _ _) _ |- _ ] => invert H
          | [ H : step _ _ |- _ ] => invert2 H
          end; simplify); equality || eauto 7.
Qed.

(* We'll return to these systems and their abstractions in the next few
 * chapters. *)


(** * Contextual small-step semantics *)

(* There is a common way to factor a small-step semantics into different parts,
 * to make the semantics easier to understand and extend.  First, we define a
 * notion of *evaluation contexts*, which are commands with *holes* in them. *)
Inductive context :=
| Hole
| CSeq (C : context) (c : cmd).

(* This relation explains how to plug the hole in a context with a specific
 * term.  Note that we use an inductive relation instead of a recursive
 * definition, because Coq's proof automation is better at working with
 * relations. *)
Inductive plug : context -> cmd -> cmd -> Prop :=
| PlugHole : forall c, plug Hole c c
| PlugSeq : forall c C c' c2,
  plug C c c'
  -> plug (CSeq C c2) c (Sequence c' c2).

(* Now we define almost the same step relation as before, with one omission:
 * only the more trivial of the [Sequence] rules remains. *)
Inductive step0 : valuation * cmd -> valuation * cmd -> Prop :=
| Step0Assign : forall v x e,
  step0 (v, Assign x e) (v $+ (x, interp e v), Skip)
| Step0Seq : forall v c2,
  step0 (v, Sequence Skip c2) (v, c2)
| Step0IfTrue : forall v e then_ else_,
  interp e v <> 0
  -> step0 (v, If e then_ else_) (v, then_)
| Step0IfFalse : forall v e then_ else_,
  interp e v = 0
  -> step0 (v, If e then_ else_) (v, else_)
| Step0WhileTrue : forall v e body,
  interp e v <> 0
  -> step0 (v, While e body) (v, Sequence body (While e body))
| Step0WhileFalse : forall v e body,
  interp e v = 0
  -> step0 (v, While e body) (v, Skip).

(* We recover the meaning of the original with one top-level rule, combining
 * plugging of contexts with basic steps. *)
Inductive cstep : valuation * cmd -> valuation * cmd -> Prop :=
| CStep : forall C v c v' c' c1 c2,
  plug C c c1
  -> step0 (v, c) (v', c')
  -> plug C c' c2
  -> cstep (v, c1) (v', c2).

(* We can prove equivalence between the two formulations. *)

Local Hint Constructors plug step0 cstep : core.

Theorem step_cstep : forall v c v' c',
  step (v, c) (v', c')
  -> cstep (v, c) (v', c').
Proof.
Admitted.

Theorem cstep_step : forall v c v' c',
  cstep (v, c) (v', c')
  -> step (v, c) (v', c').
Proof.
Admitted.






















(** * Determinism *)

(* Each of the relations we have defined turns out to be deterministic.  Let's
 * prove it. *)

Theorem eval_det : forall v c v1,
  eval v c v1
  -> forall v2, eval v c v2
  -> v1 = v2.
Proof.
  induct 1; invert 1; try first_order.

  apply IHeval2.
  apply IHeval1 in H5.
  subst.
  assumption.

  apply IHeval2.
  apply IHeval1 in H7.
  subst.
  assumption.
Qed.

Theorem step_det : forall s out1,
  step s out1
  -> forall out2, step s out2
  -> out1 = out2.
Proof.
  induct 1; invert 1; try first_order.

  apply IHstep in H5.
  equality.

  invert H.

  invert H4.
Qed.

Theorem cstep_det : forall s out1,
  cstep s out1
  -> forall out2, cstep s out2
  -> out1 = out2.
Proof.
  simplify.
  cases s; cases out1; cases out2.
  eapply step_det.
  apply cstep_step.
  eassumption.
  apply cstep_step.
  eassumption.
Qed.






























(** * Example of how easy it is to add concurrency to a contextual semantics *)

(** At this point, we add concurrency to the code we already wrote above. *)

(*
(* Here's the classic cautionary-tale program about remembering to lock your
 * concurrent threads. *)
Definition prog :=
  ("a" <- "n";;
   "n" <- "a" + 1)
  || ("b" <- "n";;
      "n" <- "b" + 1).

Local Hint Constructors plug step0 cstep : core.

(* The naive "expected" answer is attainable. *)
Theorem correctAnswer : forall n, exists v, cstep^* ($0 $+ ("n", n), prog) (v, Skip)
                                            /\ v $? "n" = Some (n + 2).
Proof.
  eexists; propositional.
  unfold prog.

  econstructor.
  eapply CStep with (C := CPar1 (CSeq Hole _) _); eauto.

  econstructor.
  eapply CStep with (C := CPar1 Hole _); eauto.

  econstructor.
  eapply CStep with (C := CPar1 Hole _); eauto.

  econstructor.
  eapply CStep with (C := Hole); eauto.

  econstructor.
  eapply CStep with (C := CSeq Hole _); eauto.

  econstructor.
  eapply CStep with (C := Hole); eauto.

  econstructor.
  eapply CStep with (C := Hole); eauto.

  econstructor.

  simplify.
  f_equal.
  ring.
Qed.

(* But so is the "wrong" answer! *)
Theorem wrongAnswer : forall n, exists v, cstep^* ($0 $+ ("n", n), prog) (v, Skip)
                                          /\ v $? "n" = Some (n + 1).
Proof.
  eexists; propositional.
  unfold prog.
Admitted.
*)
