(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 2: Basic Program Syntax
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.
(* This [Import] command is for including a library of code, theorems, tactics, etc.
 * Here we just include the standard library of the book.
 * We won't distinguish carefully between built-in Coq features and those provided by that library. *)

(* As a first example, let's look at the syntax of simple arithmetic expressions.
 * We use the Coq feature of modules, which let us group related definitions together.
 * A key benefit is that names can be reused across modules,
 * which is helpful to define several variants of a suite of functionality,
 * within a single source file. *)
Module ArithWithConstants.

  (* The following definition closely mirrors a standard BNF grammar for expressions.
   * It defines abstract syntax trees of arithmetic expressions. *)
  Inductive arith : Set :=
  | Const (n : nat)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  (* Here are a few examples of specific expressions. *)
  Example ex1 := Const 42.
  Example ex2 := Plus (Const 1) (Times (Const 2) (Const 3)).

  (* How many nodes appear in the tree for an expression?
   * Unlike in many programming languages, in Coq,
   * recursive functions must be marked as recursive explicitly.
   * That marking comes with the [Fixpoint] command, as opposed to [Definition].
   * Note also that Coq checks termination of each recursive definition.
   * Intuitively, recursive calls must be on subterms of the original argument. *)
  Fixpoint size (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Plus e1 e2 => 1 + size e1 + size e2
    | Times e1 e2 => 1 + size e1 + size e2
    end.

  (* Here's how to run a program (evaluate a term) in Coq. *)
  Compute size ex1.
  Compute size ex2.

  (* What's the longest path from the root of a syntax tree to a leaf? *)
  Fixpoint depth (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Plus e1 e2 => 1 + max (depth e1) (depth e2)
    | Times e1 e2 => 1 + max (depth e1) (depth e2)
    end.

  Compute depth ex1.
  Compute depth ex2.

  (* Our first proof!
   * Size is an upper bound on depth. *)
  Theorem depth_le_size : forall e, depth e <= size e.
  Proof.
    (* Within a proof, we apply commands called *tactics*.
     * Here's our first one.
     * Throughout the book's Coq code, we give a brief note documenting each tactic,
     * after its first use.
     * Keep in mind that the best way to understand what's going on
     * is to run the proof script for yourself, inspecting intermediate states! *)
    induct e.
    (* [induct x]: where [x] is a variable in the theorem statement,
     *   structure the proof by induction on the structure of [x].
     *   You will get one generated subgoal per constructor in the
     *   inductive definition of [x].  (Indeed, it is required that 
     *   [x]'s type was introduced with [Inductive].) *)

    simplify.
    (* [simplify]: simplify throughout the goal, applying the definitions of
     *   recursive functions directly.  That is, when a subterm
     *   matches one of the [match] cases in a defining [Fixpoint],
     *   replace with the body of that case, then repeat. *)
    linear_arithmetic.
    (* [linear_arithmetic]: a complete decision procedure for linear arithmetic.
     *   Relevant formulas are essentially those built up from
     *   variables and constant natural numbers and integers
     *   using only addition, with equality and inequality
     *   comparisons on top.  (Multiplication by constants
     *   is supported, as a shorthand for repeated addition.) *)

    simplify.
    linear_arithmetic.

    simplify.
    linear_arithmetic.
  Qed.

  Theorem depth_le_size_snazzy : forall e, depth e <= size e.
  Proof.
    induct e; simplify; linear_arithmetic.
    (* Oo, look at that!  Chaining tactics with semicolon, as in [t1; t2],
     * asks to run [t1] on the goal, then run [t2] on *every*
     * generated subgoal.  This is an essential ingredient for automation. *)
  Qed.

  (* A silly recursive function: swap the operand orders of all binary operators. *)
  Fixpoint commuter (e : arith) : arith :=
    match e with
    | Const _ => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
    end.

  Compute commuter ex1.
  Compute commuter ex2.

  (* [commuter] has all the appropriate interactions with other functions (and itself). *)

  Theorem size_commuter : forall e, size (commuter e) = size e.
  Proof.
    induct e; simplify; linear_arithmetic.
  Qed.

  Theorem depth_commuter : forall e, depth (commuter e) = depth e.
  Proof.
    induct e; simplify; linear_arithmetic.
  Qed.

  Theorem commuter_inverse : forall e, commuter (commuter e) = e.
  Proof.
    induct e; simplify; equality.
    (* [equality]: a complete decision procedure for the theory of equality
     *   and uninterpreted functions.  That is, the goal must follow
     *   from only reflexivity, symmetry, transitivity, and congruence
     *   of equality, including that functions really do behave as functions. *)
  Qed.

End ArithWithConstants.

(* Let's shake things up a bit by adding variables to expressions.
 * Note that all of the automated proof scripts from before will keep working
 * with no changes!  That sort of "free" proof evolution is invaluable for
 * theorems about real-world compilers, say. *)
Module ArithWithVariables.

  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var) (* <-- this is the new constructor! *)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  Example ex1 := Const 42.
  Example ex2 := Plus (Const 1) (Times (Var "x") (Const 3)).

  Fixpoint size (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Var _ => 1
    | Plus e1 e2 => 1 + size e1 + size e2
    | Times e1 e2 => 1 + size e1 + size e2
    end.

  Compute size ex1.
  Compute size ex2.

  Fixpoint depth (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Var _ => 1
    | Plus e1 e2 => 1 + max (depth e1) (depth e2)
    | Times e1 e2 => 1 + max (depth e1) (depth e2)
    end.

  Compute depth ex1.
  Compute depth ex2.

  Theorem depth_le_size : forall e, depth e <= size e.
  Proof.
    induct e; simplify; linear_arithmetic.
  Qed.

  Fixpoint commuter (e : arith) : arith :=
    match e with
    | Const _ => e
    | Var _ => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
    end.

  Compute commuter ex1.
  Compute commuter ex2.

  Theorem size_commuter : forall e, size (commuter e) = size e.
  Proof.
    induct e; simplify; linear_arithmetic.
  Qed.

  Theorem depth_commuter : forall e, depth (commuter e) = depth e.
  Proof.
    induct e; simplify; linear_arithmetic.
  Qed.

  Theorem commuter_inverse : forall e, commuter (commuter e) = e.
  Proof.
    induct e; simplify; equality.
  Qed.

  (* Now that we have variables, we can consider new operations,
   * like substituting an expression for a variable.
   * We use an infix operator [==v] for equality tests on strings.
   * It has a somewhat funny and very expressive type,
   * whose details we will try to gloss over.
   * (We later return to them in SubsetTypes.v.) *)
  Fixpoint substitute (inThis : arith) (replaceThis : var) (withThis : arith) : arith :=
    match inThis with
    | Const _ => inThis
    | Var x => if x ==v replaceThis then withThis else inThis
    | Plus e1 e2 => Plus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
    | Times e1 e2 => Times (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
    end.

  (* An intuitive property about how much [substitute] might increase depth. *)
  Theorem substitute_depth : forall replaceThis withThis inThis,
    depth (substitute inThis replaceThis withThis) <= depth inThis + depth withThis.
  Proof.
    induct inThis.

    simplify.
    linear_arithmetic.

    simplify.
    cases (x ==v replaceThis).
    (* [cases e]: break the proof into one case for each constructor that might have
     *   been used to build the value of expression [e].  In the special case where
     *   [e] essentially has a Boolean type, we consider whether [e] is true or false. *)
    linear_arithmetic.
    simplify.
    linear_arithmetic.

    simplify.
    linear_arithmetic.

    simplify.
    linear_arithmetic.
  Qed.

  (* Let's get fancier about automation, using [match goal] to pattern-match the goal
   * and decide what to do next!
   * The [|-] syntax separates hypotheses and conclusion in a goal.
   * The [context] syntax is for matching against *any subterm* of a term.
   * The construct [try] is also useful, for attempting a tactic and rolling back
   * the effect if any error is encountered. *)
  Theorem substitute_depth_snazzy : forall replaceThis withThis inThis,
    depth (substitute inThis replaceThis withThis) <= depth inThis + depth withThis.
  Proof.
    induct inThis; simplify;
    try match goal with
        | [ |- context[if ?a ==v ?b then _ else _] ] => cases (a ==v b); simplify
        end; linear_arithmetic.
  Qed.

  (* A silly self-substitution has no effect. *)
  Theorem substitute_self : forall replaceThis inThis,
    substitute inThis replaceThis (Var replaceThis) = inThis.
  Proof.
    induct inThis; simplify;
    try match goal with
        | [ |- context[if ?a ==v ?b then _ else _] ] => cases (a ==v b); simplify
        end; equality.
  Qed.

  (* We can do substitution and commuting in either order. *)
  Theorem substitute_commuter : forall replaceThis withThis inThis,
    commuter (substitute inThis replaceThis withThis)
    = substitute (commuter inThis) replaceThis (commuter withThis).
  Proof.
    induct inThis; simplify;
    try match goal with
        | [ |- context[if ?a ==v ?b then _ else _] ] => cases (a ==v b); simplify
        end; equality.
  Qed.

  (* *Constant folding* is one of the classic compiler optimizations.
   * We repeatedly find opportunities to replace fancier expressions
   * with known constant values. *)
  Fixpoint constantFold (e : arith) : arith :=
    match e with
    | Const _ => e
    | Var _ => e
    | Plus e1 e2 =>
      let e1' := constantFold e1 in
      let e2' := constantFold e2 in
      match e1', e2' with
      | Const n1, Const n2 => Const (n1 + n2)
      | Const 0, _ => e2'
      | _, Const 0 => e1'
      | _, _ => Plus e1' e2'
      end
    | Times e1 e2 =>
      let e1' := constantFold e1 in
      let e2' := constantFold e2 in
      match e1', e2' with
      | Const n1, Const n2 => Const (n1 * n2)
      | Const 1, _ => e2'
      | _, Const 1 => e1'
      | Const 0, _ => Const 0
      | _, Const 0 => Const 0
      | _, _ => Times e1' e2'
      end
    end.

  (* This is supposed to be an *optimization*, so it had better not *increase*
   * the size of an expression!
   * There are enough cases to consider here that we skip straight to
   * the automation.
   * A new scripting construct is [match] patterns with dummy bodies.
   * Such a pattern matches *any* [match] in a goal, over any type! *)
  Theorem size_constantFold : forall e, size (constantFold e) <= size e.
  Proof.
    induct e; simplify;
    repeat match goal with
           | [ |- context[match ?E with _ => _ end] ] => cases E; simplify
           end; linear_arithmetic.
  Qed.

  (* Business as usual, with another commuting law *)
  Theorem commuter_constantFold : forall e, commuter (constantFold e) = constantFold (commuter e).
  Proof.
    induct e; simplify;
    repeat match goal with
           | [ |- context[match ?E with _ => _ end] ] => cases E; simplify
           | [ H : ?f _ = ?f _ |- _ ] => invert H
           | [ |- ?f _ = ?f _ ] => f_equal
           end; equality || linear_arithmetic || ring.
    (* [f_equal]: when the goal is an equality between two applications of
     *   the same function, switch to proving that the function arguments are
     *   pairwise equal.
     * [invert H]: replace hypothesis [H] with other facts that can be deduced
     *   from the structure of [H]'s statement.  This is admittedly a fuzzy
     *   description for now; we'll learn much more about the logic shortly!
     *   Here, what matters is that, when the hypothesis is an equality between
     *   two applications of a constructor of an inductive type, we learn that
     *   the arguments to the constructor must be pairwise equal.
     * [ring]: prove goals that are equalities over some registered ring or
     *   semiring, in the sense of algebra, where the goal follows solely from
     *   the axioms of that algebraic structure. *)
  Qed.

  (* To define a further transformation, we first write a roundabout way of
   * testing whether an expression is a constant.
   * This detour happens to be useful to avoid overhead in concert with
   * pattern matching, since Coq internally elaborates wildcard [_] patterns
   * into separate cases for all constructors not considered beforehand.
   * That expansion can create serious code blow-ups, leading to serious
   * proof blow-ups! *)
  Definition isConst (e : arith) : option nat :=
    match e with
    | Const n => Some n
    | _ => None
    end.

  (* Our next target is a function that finds multiplications by constants
   * and pushes the multiplications to the leaves of syntax trees,
   * ideally finding constants, which can be replaced by larger constants,
   * not affecting the meanings of expressions.
   * This helper function takes a coefficient [multiplyBy] that should be
   * applied to an expression. *)
  Fixpoint pushMultiplicationInside' (multiplyBy : nat) (e : arith) : arith :=
    match e with
    | Const n => Const (multiplyBy * n)
    | Var _ => Times (Const multiplyBy) e
    | Plus e1 e2 => Plus (pushMultiplicationInside' multiplyBy e1)
                         (pushMultiplicationInside' multiplyBy e2)
    | Times e1 e2 =>
      match isConst e1 with
      | Some k => pushMultiplicationInside' (k * multiplyBy) e2
      | None => Times (pushMultiplicationInside' multiplyBy e1) e2
      end
    end.

  (* The overall transformation just fixes the initial coefficient as [1]. *)
  Definition pushMultiplicationInside (e : arith) : arith :=
    pushMultiplicationInside' 1 e.

  (* Let's prove this boring arithmetic property, so that we may use it below. *)
  Lemma n_times_0 : forall n, n * 0 = 0.
  Proof.
    linear_arithmetic.
  Qed.

  (* A fun fact about pushing multiplication inside:
   * the coefficient has no effect on depth!
   * Let's start by showing any coefficient is equivalent to coefficient 0. *)
  Lemma depth_pushMultiplicationInside'_irrelevance0 : forall e multiplyBy,
    depth (pushMultiplicationInside' multiplyBy e)
    = depth (pushMultiplicationInside' 0 e).
  Proof.
    induct e; simplify.

    linear_arithmetic.

    linear_arithmetic.

    rewrite IHe1.
    (* [rewrite H]: where [H] is a hypothesis or previously proved theorem,
     *  establishing [forall x1 .. xN, e1 = e2], find a subterm of the goal
     *  that equals [e1], given the right choices of [xi] values, and replace
     *  that subterm with [e2]. *)
    rewrite IHe2.
    linear_arithmetic.

    cases (isConst e1); simplify.

    rewrite IHe2.
    rewrite n_times_0.
    linear_arithmetic.

    rewrite IHe1.
    linear_arithmetic.
  Qed.

  (* It can be remarkably hard to get Coq's automation to be dumb enough to
   * help us demonstrate all of the primitive tactics. ;-)
   * In particular, we can redo the proof in an automated way, without the
   * explicit rewrites. *)
  Lemma depth_pushMultiplicationInside'_irrelevance0_snazzy : forall e multiplyBy,
    depth (pushMultiplicationInside' multiplyBy e)
    = depth (pushMultiplicationInside' 0 e).
  Proof.
    induct e; simplify;
    try match goal with
        | [ |- context[match ?E with _ => _ end] ] => cases E; simplify
        end; equality.
  Qed.

  (* Now the general corollary about irrelevance of coefficients for depth. *)
  Lemma depth_pushMultiplicationInside'_irrelevance : forall e multiplyBy1 multiplyBy2,
    depth (pushMultiplicationInside' multiplyBy1 e)
    = depth (pushMultiplicationInside' multiplyBy2 e).
  Proof.
    simplify.
    transitivity (depth (pushMultiplicationInside' 0 e)).
    (* [transitivity X]: when proving [Y = Z], switch to proving [Y = X]
     * and [X = Z]. *)
    apply depth_pushMultiplicationInside'_irrelevance0.
    (* [apply H]: for [H] a hypothesis or previously proved theorem,
     *   establishing some fact that matches the structure of the current
     *   conclusion, switch to proving [H]'s own hypotheses.
     *   This is *backwards reasoning* via a known fact. *)
    symmetry.
    (* [symmetry]: when proving [X = Y], switch to proving [Y = X]. *)
    apply depth_pushMultiplicationInside'_irrelevance0.
  Qed.

  (* Let's prove that pushing-inside has only a small effect on depth,
   * considering for now only coefficient 0. *)
  Lemma depth_pushMultiplicationInside' : forall e,
    depth (pushMultiplicationInside' 0 e) <= S (depth e).
  Proof.
    induct e; simplify.

    linear_arithmetic.

    linear_arithmetic.

    linear_arithmetic.

    cases (isConst e1); simplify.

    rewrite n_times_0.
    linear_arithmetic.

    linear_arithmetic.
  Qed.

  Local Hint Rewrite n_times_0.
  (* Registering rewrite hints will get [simplify] to apply them for us
   * automatically! *)

  Lemma depth_pushMultiplicationInside'_snazzy : forall e,
    depth (pushMultiplicationInside' 0 e) <= S (depth e).
  Proof.
    induct e; simplify;
    try match goal with
        | [ |- context[match ?E with _ => _ end] ] => cases E; simplify
        end; linear_arithmetic.
  Qed.

  Theorem depth_pushMultiplicationInside : forall e,
    depth (pushMultiplicationInside e) <= S (depth e).
  Proof.
    simplify.
    unfold pushMultiplicationInside.
    (* [unfold X]: replace [X] by its definition. *)
    rewrite depth_pushMultiplicationInside'_irrelevance0.
    apply depth_pushMultiplicationInside'.
  Qed.

End ArithWithVariables.
