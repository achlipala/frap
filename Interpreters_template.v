Require Import Frap.


(* We begin with a return to our arithmetic language from the last chapter,
 * adding subtraction*, which will come in handy later.
 * *: good pun, right? *)
Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Example ex1 := Const 42.
Example ex2 := Plus (Var "y") (Times (Var "x") (Const 3)).

Definition valuation := map var nat.
(* A valuation is a finite map from [var] to [nat]. *)

(* The interpreter is a fairly innocuous-looking recursive function. *)
Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    (* Note use of infix operator to look up a key in a finite map. *)
    match v $? x with
    | None => 0 (* goofy default value! *)
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
                   (* For anyone who's wondering: this [-] sticks at 0,
                    * if we would otherwise underflow. *)
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

(* Here's an example valuation, using an infix operator for map extension. *)
Definition valuation0 : valuation :=
  $0 $+ ("x", 17) $+ ("y", 3).

Theorem interp_ex1 : interp ex1 valuation0 = 42.
Proof.
  simplify.
  equality.
Qed.

Theorem interp_ex2 : interp ex2 valuation0 = 54.
Proof.
  unfold valuation0.
  simplify.
  equality.
Qed.

(* Here's the silly transformation we defined last time. *)
Fixpoint commuter (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus e1 e2 => Plus (commuter e2) (commuter e1)
  | Minus e1 e2 => Minus (commuter e1) (commuter e2)
                   (* ^-- NB: didn't change the operand order here! *)
  | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

(* Instead of proving various odds-and-ends properties about it,
 * let's show what we *really* care about: it preserves the
 * *meanings* of expressions! *)
Theorem commuter_ok : forall v e, interp (commuter e) v = interp e v.
Proof.
  admit.
Admitted.

(* Let's also revisit substitution. *)
Fixpoint substitute (inThis : arith) (replaceThis : var) (withThis : arith) : arith :=
  match inThis with
  | Const _ => inThis
  | Var x => if x ==v replaceThis then withThis else inThis
  | Plus e1 e2 => Plus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  | Minus e1 e2 => Minus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  | Times e1 e2 => Times (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  end.

(* How should we state a correctness property for [substitute]?
Theorem substitute_ok : forall v replaceThis withThis inThis,
  ...
Proof.

Qed.*)

(* Let's also defined a pared-down version of the expression-simplificaton
 * functions from last chapter. *)
Fixpoint doSomeArithmetic (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus (Const n1) (Const n2) => Const (n1 + n2)
  | Plus e1 e2 => Plus (doSomeArithmetic e1) (doSomeArithmetic e2)
  | Minus e1 e2 => Minus (doSomeArithmetic e1) (doSomeArithmetic e2)
  | Times (Const n1) (Const n2) => Const (n1 * n2)
  | Times e1 e2 => Times (doSomeArithmetic e1) (doSomeArithmetic e2)
  end.

Theorem doSomeArithmetic_ok : forall e v, interp (doSomeArithmetic e) v = interp e v.
Proof.
  admit.
Admitted.






















(* Of course, we're going to get bored if we confine ourselves to arithmetic
 * expressions for the rest of our journey.  Let's get a bit fancier and define
 * a *stack machine*, related to postfix calculators that some of you may have
 * experienced. *)
Inductive instruction :=
| PushConst (n : nat)
| PushVar (x : var)
| Add
| Subtract
| Multiply.

(* What does it all mean?  An interpreter tells us unambiguously! *)
Definition run1 (i : instruction) (v : valuation) (stack : list nat) : list nat :=
  match i with
  | PushConst n => n :: stack
  | PushVar x => (match v $? x with
                  | None => 0
                  | Some n => n
                  end) :: stack
  | Add =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 + arg2 :: stack'
    | _ => stack (* arbitrary behavior in erroneous case (stack underflow) *)
    end
  | Subtract =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 - arg2 :: stack'
    | _ => stack (* arbitrary behavior in erroneous case *)
    end
  | Multiply =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 * arg2 :: stack'
    | _ => stack (* arbitrary behavior in erroneous case *)
    end
  end.

(* That function explained how to run one instruction.
 * Here's how to run several of them. *)
Fixpoint run (is : list instruction) (v : valuation) (stack : list nat) : list nat :=
  match is with
  | nil => stack
  | i :: is' => run is' v (run1 i v stack)
  end.

(* Instead of writing fiddly stack programs ourselves, let's *compile*
 * arithmetic expressions into equivalent stack programs. *)
Fixpoint compile (e : arith) : list instruction :=
  match e with
  | Const n => PushConst n :: nil
  | Var x => PushVar x :: nil
  | Plus e1 e2 => compile e1 ++ compile e2 ++ Add :: nil
  | Minus e1 e2 => compile e1 ++ compile e2 ++ Subtract :: nil
  | Times e1 e2 => compile e1 ++ compile e2 ++ Multiply :: nil
  end.

Theorem compile_ok : forall e v, run (compile e) v nil = interp e v :: nil.
Proof.
  admit.
Admitted.



























(* Let's get a bit fancier, moving toward the level of general-purpose
 * imperative languages.  Here's a language of commands, building on the
 * language of expressions we have defined. *)
Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| Repeat (e : arith) (body : cmd).

Fixpoint selfCompose {A} (f : A -> A) (n : nat) : A -> A :=
  match n with
  | O => fun x => x
  | S n' => fun x => selfCompose f n' (f x)
  end.

Fixpoint exec (c : cmd) (v : valuation) : valuation :=
  match c with
  | Skip => v
  | Assign x e => v $+ (x, interp e v)
  | Sequence c1 c2 => exec c2 (exec c1 v)
  | Repeat e body => selfCompose (exec body) (interp e v) v
  end.

(* Let's define some programs and prove that they operate in certain ways. *)

Example factorial_ugly :=
  Sequence
    (Assign "output" (Const 1))
    (Repeat (Var "input")
            (Sequence
               (Assign "output" (Times (Var "output") (Var "input")))
               (Assign "input" (Minus (Var "input") (Const 1))))).

(* Ouch; that code is hard to read.  Let's introduce some notations to make the
 * concrete syntax more palatable.  We won't explain the general mechanisms on
 * display here, but see the Coq manual for details, or try to reverse-engineer
 * them from our examples. *)
Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";" := Sequence (at level 76).
Notation "'repeat' e 'doing' body 'done'" := (Repeat e%arith body) (at level 75).

(* OK, let's try that program again. *)
Example factorial :=
  "output" <- 1;
  repeat "input" doing
    "output" <- "output" * "input";
    "input" <- "input" - 1
  done.

(* Now we prove that it really computes factorial.
 * First, a reference implementation as a functional program. *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * fact n'
  end.

Theorem factorial_ok : forall v input,
  v $? "input" = Some input
  -> exec factorial v $? "output" = Some (fact input).
Proof.
  admit.
Admitted.



















(* One last example: let's try to do loop unrolling, for constant iteration
 * counts.  That is, we can duplicate the loop body instead of using an explicit
 * loop. *)

(* This obvious-sounding fact will come in handy: self-composition gives the
 * same result, when passed two functions that map equal inputs to equal
 * outputs. *)
Lemma selfCompose_extensional : forall {A} (f g : A -> A) n x,
  (forall y, f y = g y)
  -> selfCompose f n x = selfCompose g n x.
Proof.
  induct n; simplify; try equality.

  rewrite H.
  apply IHn.
  trivial.
Qed.

(*Theorem unroll_ok : forall c v, exec (unroll c) v = exec c v.
Proof.

Qed.*)
