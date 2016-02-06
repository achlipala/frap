(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 3: Semantics via Interpreters
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.


(* We begin with a return to our arithmetic language from the last chapter. *)
Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Times (e1 e2 : arith).

Example ex1 := Const 42.
Example ex2 := Plus (Const 1) (Times (Var "x") (Const 3)).

(* The above definition only explains what programs *look like*.
 * We also care about what they *mean*.
 * The natural meaning of an expression is the number it evaluates to.
 * Actually, it's not quite that simple.
 * We need to consider the meaning to be a function over a valuation
 * to the variables, which in turn is itself a function from variable
 * names to numbers. *)
Definition valuation := var -> nat.

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => v x
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

(* Let's sanity-check the interpretation. *)
Definition valuation0 : valuation :=
  fun x => if x ==v "x" then 17 else 23.

Compute interp ex1 valuation0.
Compute interp ex2 valuation0.

(* Here's the silly transformation we defined last time. *)
Fixpoint commuter (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus e1 e2 => Plus (commuter e2) (commuter e1)
  | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

(* Instead of proving various odds-and-ends properties about it,
 * let's show what we *really* care about: it preserves the
 * *meanings* of expressions! *)
Theorem commuter_ok : forall v e, interp (commuter e) v = interp e v.
Proof.
  induct e; simplify.

  equality.

  equality.

  linear_arithmetic.

  rewrite IHe1.
  rewrite IHe2.
  ring.
Qed.
(* Well, that's a relief! ;-) *)

(* Let's also revisit substitution. *)
Fixpoint substitute (inThis : arith) (replaceThis : var) (withThis : arith) : arith :=
  match inThis with
  | Const _ => inThis
  | Var x => if x ==v replaceThis then withThis else inThis
  | Plus e1 e2 => Plus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  | Times e1 e2 => Times (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  end.

(* The natural semantic correctness condition for substitution,
 * drawing on a helper function for adding a new mapping to a valuation *)
Definition extend_valuation (v : valuation) (x : var) (n : nat) : valuation :=
  fun y => if y ==v x then n else v y.

Theorem substitute_ok : forall v replaceThis withThis inThis,
  interp (substitute inThis replaceThis withThis) v
  = interp inThis (extend_valuation v replaceThis (interp withThis v)).
Proof.
  induct inThis; simplify; try equality.

  (* One case left after our basic heuristic:
   * the variable case, naturally!
   * A little trick: unfold a definition *before* case analysis,
   * to expose an extra spot where our test expression appears,
   * so that it can be handled by [cases] at the same time. *)
  unfold extend_valuation.
  cases (x ==v replaceThis); simplify; equality.
Qed.
(* Great; we seem to have gotten that one right, too. *)

(* Let's also defined a pared-down version of the expression-simplificaton
 * functions from last chapter. *)
Fixpoint doSomeArithmetic (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus (Const n1) (Const n2) => Const (n1 + n2)
  | Plus e1 e2 => Plus (doSomeArithmetic e1) (doSomeArithmetic e2)
  | Times (Const n1) (Const n2) => Const (n1 * n2)
  | Times e1 e2 => Times (doSomeArithmetic e1) (doSomeArithmetic e2)
  end.

Theorem doSomeArithmetic_ok : forall e v, interp (doSomeArithmetic e) v = interp e v.
Proof.
  induct e; simplify; try equality.

  cases e1; simplify; try equality.
  cases e2; simplify; equality.

  cases e1; simplify; try equality.
  cases e2; simplify; equality.
Qed.

(* Of course, we're going to get bored if we confine ourselves to arithmetic
 * expressions for the rest of our journey.  Let's get a bit fancier and define
 * a *stack machine*, related to postfix calculators that some of you may have
 * experienced. *)
Inductive instruction :=
| PushConst (n : nat)
| PushVar (x : var)
| Add
| Multiply.

(* What does it all mean?  An interpreter tells us unambiguously! *)
Definition run1 (i : instruction) (v : valuation) (stack : list nat) : list nat :=
  match i with
  | PushConst n => n :: stack
  | PushVar x => v x :: stack
  | Add =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 + arg2 :: stack'
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
  | Times e1 e2 => compile e1 ++ compile e2 ++ Multiply :: nil
  end.

(* Now, of course, we should prove our compiler correct.
 * Skip down to the next theorem to see the overall correctness statement.
 * It turns out that we need to strengthen the induction hypothesis with a
 * lemma, to push the proof through. *)
Lemma compile_ok' : forall e v is stack, run (compile e ++ is) v stack = run is v (interp e v :: stack).
Proof.
  induct e; simplify.

  equality.

  equality.

  (* Here we want to use associativity of [++], to get the conclusion to match
   * an induction hypothesis.  Let's ask Coq to search its library for lemmas
   * that would justify such a rewrite, giving a pattern with wildcards, to
   * specify the essential structure that the rewrite should match. *)
  SearchRewrite ((_ ++ _) ++ _).
  (* Ah, we see just the one! *)
  rewrite app_assoc_reverse.
  rewrite IHe1.
  rewrite app_assoc_reverse.
  rewrite IHe2.
  simplify.
  equality.

  rewrite app_assoc_reverse.
  rewrite IHe1.
  rewrite app_assoc_reverse.
  rewrite IHe2.
  simplify.
  equality.
Qed.

(* The overall theorem follows as a simple corollary. *)
Theorem compile_ok : forall e v, run (compile e) v nil = interp e v :: nil.
Proof.
  simplify.

  (* To match the form of our lemma, we need to replace [compile e] with
   * [compile e ++ nil], adding a "pointless" concatenation of the empty list.
   * [SearchRewrite] again helps us find a library lemma. *)
  SearchRewrite (_ ++ nil).
  rewrite (app_nil_end (compile e)).
  (* Note that we can use [rewrite] with explicit values of the first few
   * quantified variables of a lemma.  Otherwise, [rewrite] picks an
   * unhelpful place to rewrite.  (Try it and see!) *)

  apply compile_ok'.
  (* Direct appeal to a previously proved lemma *)
Qed.
