Require Import Frap.

(* The following definition closely mirrors a standard BNF grammar for expressions.
 * It defines abstract syntax trees of arithmetic expressions. *)
Inductive arith : Set :=
| Const (n : nat)
| Plus (e1 e2 : arith)
| Times (e1 e2 : arith).

(* Here are a few examples of specific expressions. *)
Example ex1 := Const 42.
Example ex2 := Plus (Const 1) (Times (Const 2) (Const 3)).

(* How many nodes appear in the tree for an expression? *)
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
Compute size ex2.

(* Our first proof!
 * Size is an upper bound on depth. *)
Theorem depth_le_size : forall e, depth e <= size e.
Proof.
  admit.
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
  admit.
Qed.

Theorem depth_commuter : forall e, depth (commuter e) = depth e.
Proof.
  admit.
Qed.

Theorem commuter_inverse : forall e, commuter (commuter e) = e.
Proof.
  admit.
Qed.

















(* Now we go back and add this constructor to [arith]:
   <<
  | Var (x : var)
   >>

(* Now that we have variables, we can consider new operations,
 * like substituting an expression for a variable. *)
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
  admit.
Qed.

(* A silly self-substitution has no effect. *)
Theorem substitute_self : forall replaceThis inThis,
  substitute inThis replaceThis (Var replaceThis) = inThis.
Proof.
  admit.
Qed.

(* We can do substitution and commuting in either order. *)
Theorem substitute_commuter : forall replaceThis withThis inThis,
  commuter (substitute inThis replaceThis withThis)
  = substitute (commuter inThis) replaceThis (commuter withThis).
Proof.
  admit.
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
 * the size of an expression! *)
Theorem size_constantFold : forall e, size (constantFold e) <= size e.
Proof.
  admit.
Qed.

(* Business as usual, with another commuting law *)
Theorem commuter_constantFold : forall e, commuter (constantFold e) = constantFold (commuter e).
Proof.
  admit.
Qed.

(* To define a further transformation, we first write a roundabout way of
 * testing whether an expression is a constant. *)
Definition isConst (e : arith) : option nat :=
  match e with
  | Const n => Some n
  | _ => None
  end.

(* Our next target is a function that finds multiplications by constants
 * and pushes the multiplications to the leaves of syntax trees.
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
 * Let's show that any coefficient is equivalent to coefficient 0. *)
Lemma depth_pushMultiplicationInside'_irrelevance0 : forall e multiplyBy,
  depth (pushMultiplicationInside' multiplyBy e)
  = depth (pushMultiplicationInside' 0 e).
Proof.
  admit.
Qed.

(* Let's prove that pushing-inside has only a small effect on depth,
 * considering for now only coefficient 0. *)
Lemma depth_pushMultiplicationInside' : forall e,
  depth (pushMultiplicationInside' 0 e) <= S (depth e).
Proof.
  admit.
Qed.

Theorem depth_pushMultiplicationInside : forall e,
  depth (pushMultiplicationInside e) <= S (depth e).
Proof.
  admit.
Qed.
*)
