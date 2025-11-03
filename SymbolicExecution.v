(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 16*: Symbolic Execution
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap AutomatedTheoremProving.
From Stdlib Require Import FunctionalExtensionality.

(* The last chapter explained (the beginnings of) how to automate proofs in
 * simple fragments of first-order logic, one part of the established recipe for
 * automating verification of imperative programs.  We now turn to the other
 * part: symbolic execution and other ways of algorithmically reducing program
 * correctness to problems in first-order logic. *)

(** * Our object language *)

(* Let's make a reduced copy of our language from the HoareLogic chapter.  We'll
 * omit both loops and memory access.  Loops can be handled (exercise for the
 * reader!) by interpreting a loopy program as a number of related loop-free
 * programs, connected in using loop invariants as intermediate preconditions
 * and postconditions.  We'll return to memory in the SeparationLogic chapter,
 * since there are enough nonobvious ideas there to deserve our main
 * attention. *)

Inductive exp :=
| Const (n : nat)
| Var (x : string)
| Plus (e1 e2 : exp)
| Minus (e1 e2 : exp)
| Mult (e1 e2 : exp).

Inductive bexp :=
| Equal (e1 e2 : exp)
| Less (e1 e2 : exp).

Definition valuation := fmap var nat.
Definition assertion := valuation -> Prop.

Inductive cmd :=
| Skip
| Assign (x : var) (e : exp)
| Seq (c1 c2 : cmd)
| If_ (be : bexp) (then_ else_ : cmd).

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).

Fixpoint eval (e : exp) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => v $! x
  | Plus e1 e2 => eval e1 v + eval e2 v
  | Minus e1 e2 => eval e1 v - eval e2 v
  | Mult e1 e2 => eval e1 v * eval e2 v
  end.

Definition beval (b : bexp) (v : valuation) : bool :=
  match b with
  | Equal e1 e2 => if eval e1 v ==n eval e2 v then true else false
  | Less e1 e2 => if eval e2 v <=? eval e1 v then false else true
  end.

Inductive exec : valuation -> cmd -> valuation -> Prop :=
| ExSkip : forall v,
  exec v Skip v
| ExAssign : forall v x e,
  exec v (Assign x e) (v $+ (x, eval e v))
| ExSeq : forall v1 c1 v2 c2 v3,
  exec v1 c1 v2
  -> exec v2 c2 v3
  -> exec v1 (Seq c1 c2) v3
| ExIfTrue : forall v1 b c1 c2 v2,
  beval b v1 = true
  -> exec v1 c1 v2
  -> exec v1 (If_ b c1 c2) v2
| ExIfFalse : forall v1 b c1 c2 v2,
  beval b v1 = false
  -> exec v1 c2 v2
  -> exec v1 (If_ b c1 c2) v2.

(* Now we define a further syntactic language of logical predicates, which we
 * will use in program specifications.  Recall that, in the HoareLogic chapter,
 * we used native Rocq predicates, which is convenient for integration with
 * Rocq, but now we want to show how similar functionality can be provided by
 * highly automated, standalone programs.  There is no good way for functional
 * programs in Rocq (technically the language is called "Gallina") to introspect
 * into the structure of native predicates, but we need introspection to
 * implement our automation. *)

Inductive predicate :=
| Tru
| Fals
| Exp (e : bexp)
| NotExp (e : bexp)
| And (p1 p2 : predicate)
| Or (p1 p2 : predicate)
| Ex (x : var) (p1 : predicate).
(* Note that we make our lives a *little* easy by restricting negation to apply
 * to atomic predicates only.  However, we also make our lives more than a
 * *little* tough by supporting existential quantifiers.  Below, we'll see
 * examples of how variable binding is often the biggest source of
 * administrative headache in mechanized proofs! *)

Fixpoint evalPredicate (p : predicate) (v : valuation) : Prop :=
  match p with
  | Tru => True
  | Fals => False
  | Exp e => beval e v = true
  | NotExp e => beval e v = false
  | And p1 p2 => evalPredicate p1 v /\ evalPredicate p2 v
  | Or p1 p2 => evalPredicate p1 v \/ evalPredicate p2 v
  | Ex x p1 => exists xv, evalPredicate p1 (v $+ (x, xv))
  end.

(* The start of the administrative bonanza: different functions to substitute
 * expressions for variables *)

Fixpoint subExp (inThis : exp) (replaceThis : var) (withThis : exp) : exp :=
  match inThis with
  | Const _ => inThis
  | Var x => if x ==v replaceThis then withThis else inThis
  | Plus e1 e2 => Plus (subExp e1 replaceThis withThis) (subExp e2 replaceThis withThis)
  | Minus e1 e2 => Minus (subExp e1 replaceThis withThis) (subExp e2 replaceThis withThis)
  | Mult e1 e2 => Mult (subExp e1 replaceThis withThis) (subExp e2 replaceThis withThis)
  end.

Definition subBexp (inThis : bexp) (replaceThis : var) (withThis : exp) : bexp :=
  match inThis with
  | Equal e1 e2 => Equal (subExp e1 replaceThis withThis) (subExp e2 replaceThis withThis)
  | Less e1 e2 => Less (subExp e1 replaceThis withThis) (subExp e2 replaceThis withThis)
  end.

Fixpoint subPredicate (inThis : predicate) (replaceThis : var) (withThis : exp) : predicate :=
  match inThis with
  | Tru | Fals => inThis
  | Exp e => Exp (subBexp e replaceThis withThis)
  | NotExp e => NotExp (subBexp e replaceThis withThis)
  | And p1 p2 => And (subPredicate p1 replaceThis withThis) (subPredicate p2 replaceThis withThis)
  | Or p1 p2 => Or (subPredicate p1 replaceThis withThis) (subPredicate p2 replaceThis withThis)
  | Ex x p1 => if x ==v replaceThis then
                 inThis
               else
                 Ex x (subPredicate p1 replaceThis withThis)
  end.

(* We must also define which variables appear in which places. *)

Fixpoint varInExp (e : exp) (x : var) : Prop :=
  match e with
  | Const _ => False
  | Var y => y = x
  | Plus e1 e2 | Minus e1 e2 | Mult e1 e2 => varInExp e1 x \/ varInExp e2 x
  end.

Definition varInBexp (e : bexp) (x : var) : Prop :=
  match e with
  | Equal e1 e2 | Less e1 e2 => varInExp e1 x \/ varInExp e2 x
  end.

Fixpoint varInCmd (c : cmd) (x : var) : Prop :=
  match c with
  | Skip => False
  | Assign y e => y = x \/ varInExp e x
  | Seq c1 c2 => varInCmd c1 x \/ varInCmd c2 x
  | If_ e c1 c2 => varInBexp e x \/ varInCmd c1 x \/ varInCmd c2 x
  end.

Fixpoint varInPredicate (p : predicate) (x : var) : Prop :=
  match p with
  | Tru | Fals => False
  | Exp e | NotExp e => varInBexp e x
  | And p1 p2 | Or p1 p2 => varInPredicate p1 x \/ varInPredicate p2 x
  | Ex y p1 => y = x \/ varInPredicate p1 x
  end.

(* Now the grungiest part of all: *generating fresh variable names*.  Following
 * a long mathematical tradition, we'll start with one base variable and keep
 * adding apostrophes at the end of its name, which get pronounced with
 * successively many copies of the word "prime."  (The only detail that matters
 * here is that we are able to produce a countably infinite sequence of distinct
 * variable names.) *)

Definition bumpVar (x : string) : string := x ++ "'".
Fixpoint multibumpVar (n : nat) (x : string) : string :=
  match n with
  | O => x
  | S n' => bumpVar (multibumpVar n' x)
  end.

(** * TECHNIQUE #1: Strongest Postconditions *)

(* Finally, here's our first method to automate reducing program correctness to
 * queries in first-order logic.  A *strongest-postcondition* function
 * transforms a precondition into a postcondition guaranteed to be true, after
 * running the program in an initial state satisfying the precondition.  Note
 * the bureaucratic hassle of threading through a record of which temporary
 * variable name we should use next.  You'll see that such variables are only
 * used with "exists" in explaining variable assignment, essentially the same
 * way as we built into our Hoare-logic rule for assignment. *)

Fixpoint spost (c : cmd) (nextVar : var) (p : predicate) : predicate * var :=
  match c with
  | Skip => (p, nextVar)
  | Assign x e => (Ex nextVar (And (subPredicate p x (Var nextVar)) (Exp (Equal (Var x) (subExp e x (Var nextVar))))), bumpVar nextVar)
  | Seq c1 c2 =>
      let (p, nextVar) := spost c1 nextVar p in
      spost c2 nextVar p
  | If_ e c1 c2 =>
      let (p1, nextVar) := spost c1 nextVar (And p (Exp e)) in
      let (p2, nextVar) := spost c2 nextVar (And p (NotExp e)) in
      (Or p1 p2, nextVar)
  end.
(* In fact, all of these rules should look pretty familiar from Hoare logic. *)

(* OK, now we are going to need a host of bureaucratic facts about these
 * definitions.  Feel free to skip down to the next [Theorem]. *)

Lemma eval_subExp : forall replaceThis withThis v inThis,
    eval (subExp inThis replaceThis withThis) v
    = eval inThis (v $+ (replaceThis, eval withThis v)).
Proof.
  induct inThis; simplify; auto.
  cases (x ==v replaceThis); subst; simplify; auto.
Qed.

Local Hint Rewrite eval_subExp.

Lemma eval_subBexp : forall replaceThis withThis v inThis,
    beval (subBexp inThis replaceThis withThis) v
    = beval inThis (v $+ (replaceThis, eval withThis v)).
Proof.
  induct inThis; simplify; auto.
Qed.

Local Hint Rewrite eval_subBexp.

Lemma eval_relevant : forall e v1 v2,
    (forall x, varInExp e x -> v1 $! x = v2 $! x)
    -> eval e v1 = eval e v2.
Proof.
  induct e; simplify; auto.
Qed.

Local Hint Resolve eval_relevant : core.

Lemma beval_relevant : forall e v1 v2,
    (forall x, varInBexp e x -> v1 $! x = v2 $! x)
    -> beval e v1 = beval e v2.
Proof.
  induct e; simplify;
    repeat match goal with
           | [ |- context[if ?E then _ else _] ] => cases E; simplify
           end; auto.

  rewrite eval_relevant with (v2 := v1) in n; eauto using eq_sym.
  rewrite e in n.
  exfalso; eauto.

  rewrite eval_relevant with (v2 := v2) in n; eauto using eq_sym.
  rewrite e in n.
  exfalso; eauto 6 using eq_sym.

  rewrite eval_relevant with (v2 := v1) in l0; eauto using eq_sym.
  rewrite eval_relevant with (e := e2) (v2 := v1) in l0; eauto using eq_sym.
  linear_arithmetic.

  rewrite eval_relevant with (v2 := v1) in l0; eauto using eq_sym.
  rewrite eval_relevant with (e := e1) (v2 := v1) in l0; eauto using eq_sym.
  linear_arithmetic.
Qed.

Local Hint Resolve beval_relevant : core.

Lemma evalPredicate_relevant : forall p v1 v2,
    (forall x, varInPredicate p x -> v1 $! x = v2 $! x)
    -> evalPredicate p v1 = evalPredicate p v2.
Proof.
  induct p; simplify; f_equal; eauto.

  apply functional_extensionality; simplify.
  apply IHp; simplify.
  cases (x1 ==v x); subst; simplify; auto.
Qed.

Local Hint Resolve evalPredicate_relevant : core.

Lemma eval_subPredicate : forall replaceThis withThis inThis,
    (forall x, varInPredicate inThis x
               -> varInExp withThis x
               -> False)
    -> forall v, evalPredicate (subPredicate inThis replaceThis withThis) v
                 = evalPredicate inThis (v $+ (replaceThis, eval withThis v)).
Proof.
  induct inThis; simplify; auto.

  rewrite IHinThis1; eauto.
  rewrite IHinThis2; eauto.

  rewrite IHinThis1; eauto.
  rewrite IHinThis2; eauto.

  cases (x ==v replaceThis); subst; simplify.

  f_equal.
  apply functional_extensionality; simplify.
  f_equal.
  maps_equal.

  f_equal.
  apply functional_extensionality; simplify.
  replace (v $+ (replaceThis, eval withThis v) $+ (x, x0))
    with (v $+ (x, x0) $+ (replaceThis, eval withThis v)) by maps_equal.
  rewrite eval_relevant with (e := withThis) (v2 := v $+ (x, x0)).
  apply IHinThis; eauto.
  simplify.
  assert (x1 <> x) by eauto.
  simplify.
  trivial.
Qed.

Lemma multibump_plus : forall n2 x n1,
    multibumpVar n1 (multibumpVar n2 x) = multibumpVar (n1 + n2) x.
Proof.
  induct n1; simplify; equality.
Qed.

Local Hint Rewrite multibump_plus.

Lemma spost_bumps : forall c nextVar p p' nextVar',
    spost c nextVar p = (p', nextVar')
    -> exists n, nextVar' = multibumpVar n nextVar.
Proof.
  induct c; simplify; invert H.

  exists 0; trivial.

  exists 1; trivial.

  specialize (IHc1 nextVar p).
  cases (spost c1 nextVar p).
  specialize (IHc1 _ _ eq_refl).
  invert IHc1.
  specialize (IHc2 _ _ _ _ H1).
  invert IHc2.
  eexists; simplify; eauto.

  specialize (IHc1 nextVar (And p (Exp be))).
  cases (spost c1 nextVar (And p (Exp be))).
  specialize (IHc1 _ _ eq_refl).
  invert IHc1.
  specialize (IHc2 (multibumpVar x nextVar) (And p (NotExp be))).
  cases (spost c2 (multibumpVar x nextVar) (And p (NotExp be))).
  specialize (IHc2 _ _ eq_refl).
  invert IHc2.
  invert H1.
  eexists; simplify; eauto.
Qed.

Lemma multibump_bump : forall x n,
    multibumpVar n (bumpVar x) = bumpVar (multibumpVar n x).
Proof.
  induct n; simplify; equality.
Qed.

Local Hint Rewrite multibump_bump.

Lemma length_bump : forall x,
    String.length (bumpVar x) = S (String.length x).
Proof.
  induct x; simplify; auto.
Qed.

Local Hint Rewrite length_bump.

Lemma length_multibump : forall n x,
    String.length (multibumpVar n x) = n + String.length x.
Proof.
  induct n; simplify; auto.
Qed.

Local Hint Rewrite length_multibump.

Lemma multibump_inj : forall x n m,
    multibumpVar n x = multibumpVar m x
    -> n = m.
Proof.
  simplify.
  apply (f_equal String.length) in H.
  simplify.
  linear_arithmetic.
Qed.

Lemma varIn_subExp_fwd : forall x e y e',
    varInExp (subExp e' x e) y
    -> varInExp e' y \/ varInExp e y.
Proof.
  induct e'; simplify; propositional.
  cases (x0 ==v x); simplify; subst; auto.
Qed.

Lemma varIn_subBexp_fwd : forall x e y be,
    varInBexp (subBexp be x e) y
    -> varInBexp be y \/ varInExp e y.
Proof.
  induct be; simplify; propositional;
    repeat match goal with
           | [ H : varInExp _ _ |- _ ] => apply varIn_subExp_fwd in H
           end; propositional.
Qed.

Lemma varIn_subPredicate_fwd : forall x e y p,
    varInPredicate (subPredicate p x e) y
    -> varInPredicate p y \/ varInExp e y.
Proof.
  induct p; simplify; propositional;
    repeat match goal with
           | [ H : varInBexp _ _ |- _ ] => apply varIn_subBexp_fwd in H
           end; propositional.
  cases (x0 ==v x); simplify; subst; propositional.
Qed.

Lemma spost_avoids : forall c nextVar p p' nextVar',
    spost c nextVar p = (p', nextVar')
    -> (forall x n, varInCmd c x \/ varInPredicate p x
                    -> x <> multibumpVar n nextVar)
    -> forall n, varInPredicate p' (multibumpVar n nextVar')
                 -> False.
Proof.
  induct c; simplify; invert H; simplify.

  specialize (H0 (multibumpVar n nextVar') n).
  equality.

  propositional.
  apply multibump_inj with (n := 0) (m := S n) in H; equality.
  apply varIn_subPredicate_fwd in H1.
  change (bumpVar (multibumpVar n nextVar)) with (multibumpVar (S n) nextVar) in *.
  propositional; eauto.
  simplify.
  apply multibump_inj with (n := 0) (m := S n) in H; equality.
  change (bumpVar (multibumpVar n nextVar)) with (multibumpVar (S n) nextVar) in *; eauto.
  apply varIn_subExp_fwd in H.
  change (bumpVar (multibumpVar n nextVar)) with (multibumpVar (S n) nextVar) in *.
  propositional; eauto.
  simplify.
  apply multibump_inj with (n := 0) (m := S n) in H1; equality.
  
  specialize (IHc1 nextVar p).
  cases (spost c1 nextVar p).
  specialize (IHc1 _ _ eq_refl).
  specialize (IHc2 _ _ _ _ H3).
  apply spost_bumps in Heq; invert Heq.
  apply spost_bumps in H3; invert H3.
  apply IHc2 with (n := n); simplify; eauto.
  propositional; subst; simplify; eauto.
  apply IHc1 with (n := n0); simplify; eauto.
  propositional; subst; simplify; eauto.

  specialize (IHc1 nextVar (And p (Exp be))).
  cases (spost c1 nextVar (And p (Exp be))).
  specialize (IHc1 _ _ eq_refl).
  specialize (IHc2 s (And p (NotExp be))).
  cases (spost c2 s (And p (NotExp be))).
  invert H3.
  specialize (IHc2 _ _ eq_refl).
  apply spost_bumps in Heq; invert Heq.
  apply spost_bumps in Heq0; invert Heq0.
  simplify; propositional.
  apply IHc1 with (n := n + x0); simplify; subst; eauto.
  propositional; eauto.
  apply IHc2 with (n := n); simplify; subst; eauto.
  2: rewrite Nat.add_assoc; auto.
  propositional; eauto.
Qed.

(* The fundamental soundness property of strongest postcondition!  We even
 * manage to write it with just one little administrative condition on variable
 * names. *)

Theorem spost_sound : forall v c v',
    exec v c v'
    -> forall nextVar p, evalPredicate p v

                         -> (forall x n, varInCmd c x \/ varInPredicate p x
                                         -> x <> multibumpVar n nextVar)
                         (* In other words, none of the temporary variable names
                          * we might generate is in the command or
                          * precondition. *)

                         -> evalPredicate (fst (spost c nextVar p)) v'.
Proof.
  induct 1; simplify; auto.

  exists (v $! x); simplify; propositional.
  rewrite eval_subPredicate; simplify; subst; eauto.
  rewrite evalPredicate_relevant with (v2 := v); auto.
  simplify.
  cases (x0 ==v x); subst; simplify; auto.
  cases (x0 ==v nextVar); subst; simplify; auto.
  specialize (H0 nextVar 0); simplify; exfalso; eauto.
  specialize (H0 x0 0); simplify; eauto.
  assert (x <> nextVar) by (specialize (H0 x 0); eauto).
  simplify.
  match goal with
  | [ |- context[eval ?E ?V1 ==n eval ?E ?V2] ] =>
      rewrite eval_relevant with (v1 := V2) (v2 := V1);
      cases (eval E V1 ==n eval E V1); try equality
  end.
  simplify.
  cases (x0 ==v x); subst; simplify; auto.
  cases (x0 ==v nextVar); subst; simplify; auto.
  specialize (H0 nextVar 0); simplify; exfalso; eauto.

  specialize (IHexec1 nextVar p).
  cases (spost c1 nextVar p); simplify; propositional.
  apply IHexec2.
  apply H3; propositional; eauto.
  propositional; subst; eauto.
  apply spost_bumps in Heq; invert Heq; simplify; eauto.
  eapply spost_avoids; eauto.
  propositional; eauto.

  specialize (IHexec nextVar (And p (Exp b))).
  cases (spost c1 nextVar (And p (Exp b))).
  cases (spost c2 s (And p (NotExp b))).
  simplify.
  left.
  apply IHexec; propositional; subst; eauto.

  cases (spost c1 nextVar (And p (Exp b))).
  specialize (IHexec s (And p (NotExp b))).
  cases (spost c2 s (And p (NotExp b))).
  simplify.
  right.
  apply spost_bumps in Heq; invert Heq.
  apply IHexec; propositional; subst; simplify; eauto; equality.
Qed.

(* OK, let's see our machinery in action on a few example programs. *)

Example ex1 := Seq (Assign "x" (Const 17)) (Assign "y" (Plus (Var "x") (Const 23))).
Compute fst (spost ex1 "X" Tru).

Example ex2 := Seq
                 (Seq (Assign "x" (Const 17)) (Assign "y" (Plus (Var "x") (Var "z"))))
                 (Assign "x" (Mult (Var "y") (Const 3))).
Compute fst (spost ex2 "X" Tru).

Example ex3 := If_ (Equal (Var "x") (Var "y"))
                   (Assign "z" (Mult (Var "x") (Const 2)))
                   (Assign "z" (Plus (Var "x") (Var "y"))).
Compute fst (spost ex3 "X" Tru).

(* These next two facts will be useful for automating proof of the side
 * condition we included in the soundness theorem. *)

Lemma multibump_first' : forall x0 x n,
    multibumpVar n (String x0 x) = String x0 (multibumpVar n x).
Proof.
  induction n; simplify; auto.
  rewrite IHn.
  unfold bumpVar.
  simplify.
  auto.
Qed.

Lemma multibump_first : forall x0 x n y0 y,
    String x0 x = multibumpVar n (String y0 y)
    -> x0 <> y0
    -> False.
Proof.
  simplify.
  rewrite multibump_first' in H.
  equality.
Qed.

Local Hint Extern 1 False => eapply multibump_first; [ eassumption | equality ] : core.

Theorem ex1_correct : forall v v',
    exec v ex1 v'
    -> v' $! "y" = 40.
Proof.
  simplify.
  apply spost_sound with (nextVar := "X") (p := Tru) in H.

  simplify.
  unfold bumpVar in *; simplify.
  first_order.
  simplify.
  repeat match goal with
         | [ H : context[if ?E then _ else _] |- _ ] => cases E; try equality
         end.
  linear_arithmetic.

  simplify.
  trivial.

  simplify.
  propositional; subst; auto.
Qed.

Theorem ex2_correct : forall v v',
    exec v ex2 v'
    -> v' $! "y" = 17 + v $! "z".
Proof.
  simplify.
  apply spost_sound with (nextVar := "X") (p := Exp (Equal (Var "z") (Const (v $! "z")))) in H.

  simplify.
  unfold bumpVar in *; simplify.
  first_order.
  simplify.
  repeat match goal with
         | [ H : context[if ?E then _ else _] |- _ ] => cases E; try equality
         end.
  linear_arithmetic.

  simplify.
  repeat match goal with
         | [ |- context[if ?E then _ else _] ] => cases E; equality
         end.

  simplify.
  propositional; subst; auto.
Qed.

Theorem ex3_correct : forall v v',
    exec v ex3 v'
    -> v' $! "z" = v $! "x" + v $! "y".
Proof.
  simplify.
  apply spost_sound with (nextVar := "X")
                         (p := And (Exp (Equal (Var "x") (Const (v $! "x"))))
                                   (Exp (Equal (Var "y") (Const (v $! "y"))))) in H.

  simplify.
  unfold bumpVar in *; simplify.
  first_order; simplify;
  repeat match goal with
         | [ H : context[if ?E then _ else _] |- _ ] => cases E; try equality
         end; linear_arithmetic.

  simplify.
  repeat match goal with
         | [ |- context[if ?E then _ else _] ] => cases E; try equality
         end.

  simplify.
  propositional; subst; auto.
Qed.

(* We did those proofs moderately manually, because the story isn't over yet.
 * We still proved an important implication from the calculated strongest
 * postcondition to the postcondition of interest.  We want to automate that
 * step, too. *)

(** * SHARED TOOL: A Simple First-Order Theorem Prover *)

(* Last chapter, we built a simple automated theorem prover that only
 * understands equality on variables.  We can wrap it to create an incomplete
 * but sound prover for the predicate language we have just defined. *)

(* We will consider all of the conjunctions of *atoms* implied by a larger
 * predicate. *)
Record atom := {
    Condition : bexp;
    Value : bool
  }.

(* A *scenario* pairs atoms with existential quantifiers. *)
Record scenario := {
    ExVars : list var;
    Atoms : list atom
  }.

(* Sometimes we want to combine two lists of scenarios into lists of larger
 * scenarios, each formed by combining a scenario from each list.  This function
 * generalizes that process, in the style of Cartesian products. *)
Fixpoint cross {A} (f : A -> A -> A) (ls1 ls2 : list A) : list A :=
  match ls1 with
  | [] => []
  | l1 :: ls1' => map (f l1) ls2 ++ cross f ls1' ls2
  end.

(* Now it is not too bad to translate a predicate into a list of flat
 * scenarios. *)
Fixpoint scenarios (p : predicate) : list scenario :=
  match p with
  | Tru => [{| ExVars := []; Atoms := [] |}]
  | Fals => [] (* A contradictory situation has no possible scenarios! *)
  | Exp e => [{| ExVars := []; Atoms := {| Condition := e; Value := true |} :: [] |}]
  | NotExp e => [{| ExVars := []; Atoms := {| Condition := e; Value := false |} :: [] |}]
  | And p1 p2 => cross (fun sc1 sc2 => {| ExVars := sc1.(ExVars) ++ sc2.(ExVars);
                                         Atoms := sc1.(Atoms) ++ sc2.(Atoms) |})
                       (scenarios p1) (scenarios p2)
  | Or p1 p2 => scenarios p1 ++ scenarios p2
  | Ex x p1 => map (fun sc => {| ExVars := x :: sc.(ExVars);
                                Atoms := sc.(Atoms) |}) (scenarios p1)
  end.

Compute scenarios (fst (spost ex1 "X" Tru)).
Compute scenarios (fst (spost ex2 "X" Tru)).
Compute scenarios (fst (spost ex3 "X" Tru)).

(* While we already defined how to compute which variables appear in a
 * predicate, let's now distinguish the *bound* variables that occur as
 * immediate arguments to quantifiers. *)

Fixpoint boundVars (p : predicate) : list var :=
  match p with
  | Tru | Fals | Exp _ | NotExp _ => []
  | And p1 p2 | Or p1 p2 => boundVars p1 ++ boundVars p2
  | Ex x p1 => x :: boundVars p1
  end.

Local Hint Rewrite app_nil_r.

Lemma boundVars_subPredicate : forall x e p,
    boundVars (subPredicate p x e) = boundVars p.
Proof.
  induct p; simplify; try equality.
  cases (x0 ==v x); simplify; equality.
Qed.

Local Hint Rewrite boundVars_subPredicate.

Lemma In_boundVars : forall x p,
    In x (boundVars p)
    -> varInPredicate p x.
Proof.
  induct p; simplify; propositional.
  apply in_app_or in H; propositional.
  apply in_app_or in H; propositional.
Qed.

Local Hint Resolve In_boundVars : core.

Lemma multibump_zero : forall x,
    x = multibumpVar 0 x.
Proof.
  trivial.
Qed.

Local Hint Resolve multibump_zero : core.

(* We must characterize the lack of duplicate bound ("exists") variables, with
 * the catch that duplicates between branches of "or"s are fine.  (Abbreviation
 * "wf" by convention stands for "well-formed.") *)
Fixpoint wfPredicate (p : predicate) : Prop :=
  match p with
  | Tru | Fals | Exp _ | NotExp _ => True
  | And p1 p2 => wfPredicate p1 /\ wfPredicate p2
                 /\ (forall x, In x (boundVars p1) -> varInPredicate p2 x -> False)
                 /\ (forall x, In x (boundVars p2) -> varInPredicate p1 x -> False)
  | Or p1 p2 => wfPredicate p1 /\ wfPredicate p2
  | Ex x p1 => wfPredicate p1 /\ ~In x (boundVars p1)
  end.

(* Now another sea of lemmas.  Meet me at [Theorem]? *)

Lemma varIn_subExp : forall x e' x' e,
    varInExp (subExp e x e') x'
    -> varInExp e x' \/ varInExp e' x'.
Proof.
  induct e; simplify; propositional.
  cases (x0 ==v x); subst; simplify; auto.
Qed.

Lemma varIn_subBexp : forall x e' x' e,
    varInBexp (subBexp e x e') x'
    -> varInBexp e x' \/ varInExp e' x'.
Proof.
  induct e; simplify; propositional;
    repeat match goal with
           | [ H : varInExp _ _ |- _ ] => apply varIn_subExp in H; propositional
           end.
Qed.

Lemma sub_wfPredicate : forall x e p,
    wfPredicate p
    -> (forall y, varInExp e y -> varInPredicate p y -> False)
    -> wfPredicate (subPredicate p x e).
Proof.
  induct p; simplify; first_order.

  apply varIn_subPredicate_fwd in H5; propositional; eauto.

  apply varIn_subPredicate_fwd in H5; propositional; eauto.

  cases (x0 ==v x); subst; simplify; auto.
  first_order.
Qed.

Local Hint Resolve sub_wfPredicate : core.

Lemma spost_binds : forall x c nextVar p,
    In x (boundVars (fst (spost c nextVar p)))
    -> In x (boundVars p) \/ exists n, x = multibumpVar n nextVar.
Proof.
  induct c; simplify; propositional; subst; eauto.

  specialize (IHc1 nextVar p).
  cases (spost c1 nextVar p); simplify.
  specialize (IHc2 s p0).
  cases (spost c2 s p0); simplify.
  apply spost_bumps in Heq; invert Heq.
  propositional.
  invert H1.
  right; exists (x1 + x0); simplify; trivial.

  specialize (IHc1 nextVar (And p (Exp be))).
  cases (spost c1 nextVar (And p (Exp be))).
  specialize (IHc2 s (And p (NotExp be))).
  cases (spost c2 s (And p (NotExp be))).
  simplify.
  apply in_app_or in H; first_order; subst.
  apply spost_bumps in Heq; invert Heq.
  right.
  exists (x0 + x); simplify; trivial.
Qed.

Lemma spost_uses : forall x c nextVar p,
    varInPredicate (fst (spost c nextVar p)) x
    -> varInPredicate p x \/ varInCmd c x \/ exists n, x = multibumpVar n nextVar.
Proof.
  induct c; simplify; propositional; subst; eauto.

  apply varIn_subPredicate_fwd in H; simplify; propositional; subst; eauto.

  apply varIn_subExp_fwd in H0; simplify; propositional; subst; eauto.

  specialize (IHc1 nextVar p).
  cases (spost c1 nextVar p); simplify.
  specialize (IHc2 s p0).
  cases (spost c2 s p0); simplify.
  apply spost_bumps in Heq; invert Heq.
  first_order.
  simplify.
  eauto.

  specialize (IHc1 nextVar (And p (Exp be))).
  cases (spost c1 nextVar (And p (Exp be))).
  specialize (IHc2 s (And p (NotExp be))).
  cases (spost c2 s (And p (NotExp be))).
  simplify.
  first_order.
  apply spost_bumps in Heq; invert Heq.
  simplify.
  eauto.
Qed.

Lemma spost_wf : forall c nextVar p,
    wfPredicate p
    -> (forall x n, varInCmd c x \/ varInPredicate p x
                    -> x <> multibumpVar n nextVar)
    -> (forall x, varInCmd c x -> In x (boundVars p) -> False)
    -> wfPredicate (fst (spost c nextVar p)).
Proof.
  induct c; simplify; propositional; eauto.

  apply sub_wfPredicate; auto.
  simplify; subst; eauto.

  apply varIn_subExp in H4; simplify; propositional; subst; eauto.

  specialize (IHc1 nextVar p).
  cases (spost c1 nextVar p); simplify; propositional.
  specialize (spost_bumps _ _ _ _ _ Heq); invert 1.
  apply IHc2; propositional; subst; simplify; eauto.
  first_order.
  eapply spost_avoids; eauto.
  propositional; eauto.
  simplify.
  eassumption.

  specialize (spost_binds x0 c1 nextVar p).
  rewrite Heq; simplify.
  first_order.
  
  specialize (IHc1 nextVar (And p (Exp be))).
  cases (spost c1 nextVar (And p (Exp be))); simplify; propositional.
  specialize (IHc2 s (And p (NotExp be))).
  specialize (spost_bumps _ _ _ _ _ Heq); invert 1.
  cases (spost c2 (multibumpVar x nextVar) (And p (NotExp be))); simplify; propositional.
  apply H2; propositional; eauto.
  apply H3; propositional; subst; simplify; eauto.
Qed.

Local Hint Resolve includes_refl : core.

Lemma Exists_cross : forall A (f : A -> A -> A) (P P1 P2 : A -> Prop) (ls1 ls2 : list A),
    Exists P1 ls1
    -> Exists P2 ls2
    -> (forall l1 l2,
           In l1 ls1
           -> P1 l1
           -> In l2 ls2
           -> P2 l2
           -> P (f l1 l2))
    -> Exists P (cross f ls1 ls2).
Proof.
  induct 1; simplify.

  apply Exists_app.
  left.
  apply Exists_map.
  apply Exists_exists in H0; invert H0; propositional.
  apply Exists_exists; eauto.  

  apply Exists_app.
  auto.
Qed.

Lemma Forall_cross : forall A (f : A -> A -> A) (P P1 P2 : A -> Prop) (ls1 ls2 : list A),
    Forall P1 ls1
    -> Forall P2 ls2
    -> (forall l1 l2,
           P1 l1
           -> P2 l2
           -> P (f l1 l2))
    -> Forall P (cross f ls1 ls2).
Proof.
  induct 1; simplify; eauto.

  apply Forall_app; propositional.
  apply Forall_map.
  eapply Forall_impl; eauto.
Qed.

Local Hint Resolve in_or_app lookup_Some_dom lookup_None_dom : core.

Lemma includes_join : forall {A B} (m m1 m2 : fmap A B),
    m $<= m1
    -> m $<= m2
    -> m $<= m1 $++ m2.
Proof.
  simplify.
  apply includes_intro; simplify.
  rewrite lookup_join1.
  eapply includes_lookup in H1; eassumption.
  eauto.
Qed.

Local Hint Resolve includes_join : core.

Lemma scenarios_dom : forall p,
    List.Forall (fun sc =>
                   List.Forall (fun a =>
                                  forall x, varInBexp a.(Condition) x
                                            -> varInPredicate p x) sc.(Atoms)) (scenarios p).
Proof.
  induct p; simplify; eauto.

  constructor; simplify; auto.

  constructor; simplify; auto.

  eapply Forall_cross; eauto; simplify.
  eapply Forall_app; propositional; eapply Forall_impl; try eassumption; simplify; eauto.

  apply Forall_app; propositional; eapply Forall_impl; try eassumption; simplify;
    eapply Forall_impl; try eassumption; eauto.

  apply Forall_map.
  eapply Forall_impl; try eassumption; eauto.
  simplify; eapply Forall_impl; try eassumption; eauto.
Qed.

Local Hint Unfold incl : core.
Local Hint Resolve incl_app_app : core.

Lemma scenarios_bound : forall p,
    List.Forall (fun sc => incl sc.(ExVars) (boundVars p)) (scenarios p).
Proof.
  induct p; simplify; eauto.

  eapply Forall_cross; eauto; simplify; eauto.

  apply Forall_app; unfold incl in *; propositional.
  eapply Forall_impl; try eassumption; simplify; eauto.
  eapply Forall_impl; try eassumption; simplify; eauto.

  apply Forall_map; simplify.
  eapply Forall_impl; try eassumption; simplify.
  apply incl_cons; simplify; auto.
  apply incl_tl; assumption.
Qed.

Lemma Forall_In : forall A (P : A -> Prop) x ls,
    Forall P ls
    -> In x ls
    -> P x.
Proof.
  induct 1; simplify; propositional; subst; auto.
Qed.

(* This next little bit was one of the most surprising detours in the proof.  To
 * be compatible with assumptions by the AutomatedTheoremProving library, we
 * have to make sure valuations include values for all variables that predicates
 * might mention; so we zero out any variables not yet included. *)
Fixpoint zeroAll (xs : list var) (v : valuation) : valuation :=
  match xs with
  | nil => v
  | x :: xs' => zeroAll xs' v $+ (x, 0)
  end.

Lemma includes_trans : forall A B (m1 m2 m3 : fmap A B),
    m1 $<= m2
    -> m2 $<= m3
    -> m1 $<= m3.
Proof.
  simplify; apply includes_intro; eauto.
Qed.

Lemma lookup_zeroAll_changed : forall xs v x,
    In x xs
    -> zeroAll xs v $? x = Some 0.
Proof.
  induct xs; simplify; propositional; subst; simplify; auto.
  cases (a ==v x); subst; simplify; auto.
Qed.

Lemma lookup_zeroAll_unchanged : forall xs v x,
    ~In x xs
    -> zeroAll xs v $? x = v $? x.
Proof.
  induct xs; simplify; propositional; subst; simplify; auto.
Qed.

Local Hint Rewrite lookup_zeroAll_changed lookup_zeroAll_unchanged using equality.

Lemma includes_zeroAll : forall xs v,
    List.Forall (fun x => v $? x = None) xs
    -> v $<= zeroAll xs v.
Proof.
  simplify.
  apply includes_intro; simplify.
  cases (in_dec var_eq k xs); simplify; auto.
  eapply Forall_forall in H; eauto.
  equality.
Qed.

Definition evalCondition (v : valuation) (a : atom) :=
  beval a.(Condition) v = a.(Value).

(* OK, what does it mean for scenarios to be implemented correctly to use in
 * analyzing the *lefthand* side of an implication? *)
Theorem scenarios_sound : forall p v,
    evalPredicate p v
    -> wfPredicate p
    -> (forall x, In x (boundVars p) -> v $? x = None)

    (* First, we use [Exists] to capture how there is *some* scenario compatible
     * with any valuation that the predicate accepts.  All other scenarios could
     * be incompatible, or there could be multiple options. *)
    -> List.Exists (fun sc =>
                      (* Second, we assert there exists an *extension* of the
                       * valuation, stocked with the right values for
                       * existential variables. *)
                      exists v', v $<= v'
                                 /\ (forall x, v $? x = None
                                               -> v' $? x <> None
                                               -> In x sc.(ExVars))

                                 (* In this extension, all atoms are valid. *)
                                 /\ List.Forall (evalCondition v') sc.(Atoms)) (scenarios p).
Proof.
  induct p; simplify; propositional; eauto 7.

  constructor.
  eexists; propositional; eauto; simplify; eauto.

  constructor.
  eexists; propositional; eauto; simplify; eauto.

  constructor.
  eexists; propositional; eauto; simplify; eauto.
  
  apply IHp1 in H2; eauto.
  apply IHp2 in H3; eauto.
  eapply Exists_cross; try eassumption; simplify.
  invert H7; invert H9; propositional.
  exists (x $++ x0); propositional; eauto.
  cases (x $? x1).
  assert (x $? x1 <> None) by equality.
  eauto.
  rewrite lookup_join2 in H15 by eauto.
  apply in_or_app; eauto.
  apply Forall_app; propositional.

  unfold evalCondition in *.
  apply Forall_forall; simplify.
  eapply Forall_In in H13; try eassumption.
  rewrite <- H13.
  apply beval_relevant; simplify.
  cases (v $? x2).
  rewrite lookup_join1 by eauto.
  trivial.
  cases (x $? x2).
  rewrite lookup_join1 by eauto.
  rewrite Heq0; trivial.
  rewrite lookup_join2 by eauto.
  cases (x0 $? x2); auto.
  exfalso.
  assert (x0 $? x2 <> None) by equality.
  specialize (scenarios_bound p2); intro Hforall.
  eapply Forall_forall in Hforall; try eassumption.
  eapply H6; eauto.
  specialize (scenarios_dom p1); intro Hdom.
  do 2 (eapply Forall_forall in Hdom; try eassumption).
  eauto.

  unfold evalCondition in *.
  apply Forall_forall; simplify.
  eapply Forall_In in H14; try eassumption.
  rewrite <- H14.
  apply beval_relevant; simplify.
  cases (v $? x2).
  rewrite lookup_join1 by eauto.
  eapply includes_lookup in H10; eauto.
  eapply includes_lookup in H9; eauto.
  rewrite H9, H10; trivial.
  cases (x $? x2).
  rewrite lookup_join1 by eauto.
  exfalso.
  assert (x $? x2 <> None) by equality.
  specialize (scenarios_bound p1); intro Hforall.
  eapply Forall_forall in Hforall; try eassumption.
  eapply H4; eauto.
  specialize (scenarios_dom p2); intro Hdom.
  do 2 (eapply Forall_forall in Hdom; try eassumption).
  eauto.
  rewrite lookup_join2 by eauto.
  trivial.

  apply Exists_app; eauto 6.

  apply Exists_app; eauto 6.

  apply Exists_map; simplify.
  invert H.
  eapply Exists_impl; try apply IHp; eauto.
  simplify.
  invert H.
  propositional.
  exists x1; propositional.
  apply includes_intro; simplify.
  cases (k ==v x); subst; simplify; auto.
  rewrite H1 in H5; equality.
  eapply includes_lookup in H; eauto.
  simplify; assumption.
  cases (x ==v x2); auto.
  right.
  apply H4; simplify; auto.
  
  simplify; eauto.
Qed.

(* A few lemmas before we move on *)

Lemma cross_nil : forall A (f : A -> A -> A) ls1,
    cross f ls1 [] = [].
Proof.
  induct ls1; simplify; auto.
Qed.

Local Hint Rewrite cross_nil length_map length_app.

Lemma length_cross : forall A (f : A -> A -> A) ls1 ls2,
    length (cross f ls1 ls2) = length ls1 * length ls2.
Proof.
  induct ls1; simplify; auto.
Qed.

Lemma cross_singleton : forall A (f : A -> A -> A) ls1 ls2 v,
    cross f ls1 ls2 = [v]
    -> exists l1 l2, ls1 = [l1] /\ ls2 = [l2] /\ v = f l1 l2.
Proof.
  simplify.
  specialize (length_cross _ f ls1 ls2).
  rewrite H.
  simplify.
  cases ls1; simplify; try equality.
  cases ls2; simplify; try equality.
  cases ls2; simplify; try equality.
  cases ls1; simplify; try equality.
  invert H.
  eauto.
Qed.

(* Here is a characterization of [scenarios] soundness when used to prove the
 * *righthand* side of an implication.  We focus on the simple case of one
 * scenario with no quantifiers (just to make the proofs easier while showing
 * off the main ideas of the approach). *)

Theorem scenarios_bwd : forall p ats v,
    scenarios p = [{| ExVars := []; Atoms := ats |}]
    -> List.Forall (evalCondition v) ats
    -> evalPredicate p v.
Proof.
  induct p; simplify; propositional; try equality.

  invert H.
  invert H0.
  assumption.

  invert H.
  invert H0.
  assumption.

  apply cross_singleton in H; first_order.
  invert H2.
  cases x; cases x0; simplify.
  cases ExVars0; simplify; try equality.
  subst.
  apply Forall_app in H0.
  propositional.
  eauto.

  apply cross_singleton in H; first_order.
  invert H2.
  cases x; cases x0; simplify.
  cases ExVars0; simplify; try equality.
  subst.
  apply Forall_app in H0.
  propositional.
  eauto.

  cases (scenarios p1); simplify; eauto.
  invert H.
  cases l; simplify; try equality.
  eauto.

  cases (scenarios p); simplify; equality.
Qed.

Local Hint Resolve spost_wf : core.

Lemma exec_changes : forall x v c v',
    exec v c v'
    -> v' $? x <> v $? x
    -> varInCmd c x.
Proof.
  induct 1; simplify; try equality.

  cases (x ==v x0); subst; simplify; equality.

  cases (v3 $? x); cases (v2 $? x); try equality.
  cases (n ==n n0); subst; auto.
  right; apply IHexec2; equality.
Qed.

(* Now we are ready to define our automated prover.  First, two functions that
 * respectively record all known equalities and confirm provability of all
 * required equalities.  They use the monadic notation and library functions
 * from last chapter, which we are glad now to treat as black boxes, in the
 * style of data abstraction. *)

Fixpoint assertAll (ats : list atom) : M unit :=
  match ats with
  | nil => ret tt
  | {| Condition := Equal (Var x) (Var y); Value := true |} :: ats' =>
      (_ <- assertEqual x y; assertAll ats')
  | _ :: ats' => assertAll ats'
  end.
(* Note that we conservatively ignore all atoms that our prover doesn't know how
 * to handle.  In dealing with the *lefthand* side of an implication, it is
 * always sound to forget information. *)

Fixpoint checkAll (ats : list atom) : M bool :=
  match ats with
  | nil => ret true
  | {| Condition := Equal (Var x) (Var y); Value := true |} :: ats' =>
      (b <- checkEqual x y;
       if b then
         checkAll ats'
       else
         ret false)
  | _ :: ats' => ret false
  end.
(* In contrast, here the checker must abort (return [false]) when it encounters
 * a fact not supported by the prover. *)

(* Our overall entailment checker combines the two routines and kicks off the
 * monadic computation in an empty e-graph. *)
Definition entailment (lhs rhs : list atom) : bool :=
  snd ((_ <- assertAll lhs;
        checkAll rhs) empty).

(* One more little wrapper implements our checker for a claimed Hoare triple. *)
Definition verify_computable (pre : predicate) (c : cmd) (post : predicate) :=
  match scenarios post with
  | [{| ExVars := []; Atoms := apost |}] =>
      (* Note above: we simplify by forcing the postcondition to have a very
       * regular, quantifier-free structure. *)
      forallb (fun lhs => entailment lhs.(Atoms) apost)
              (scenarios (fst (spost c "X" pre)))
  | _ => false
  end.

(* Now a nontrivial proof of soundness for that checker: *)

Local Hint Resolve Forall_inv_tail : core.

Lemma wpre_assertAll : forall ats Q g,
    (forall g',
        (forall v, rep g {| Values := v |}
                   -> Forall (fun a => forall x, varInBexp a.(Condition) x
                                                 -> v $? x <> None) ats
                   -> Forall (evalCondition v) ats
                   -> rep g' {| Values := v |})
        -> Q g' tt)
    -> wpre (assertAll ats) Q g.
Proof.
  induct ats; simplify.

  apply wpre_ret; auto.

  cases a.
  cases Condition0; eauto 6.
  cases e1; eauto 6.
  cases e2; eauto 6.
  cases Value0; eauto 6.
  apply wpre_bind.
  apply wpre_assertEqual; simplify.
  apply IHats; simplify.
  apply H; simplify.
  apply H1; eauto.
  rewrite H0.
  split; auto.
  invert H3.
  invert H4.
  simplify.
  red in H6; red.
  simplify.
  cases (v $! x ==n v $! x0); try equality.
  cases (v $? x).
  cases (v $? x0).
  equality.
  exfalso; eapply H7; eauto.
  exfalso; eapply H7; [ | eauto ]; auto.
Qed.

Lemma wpre_checkAll : forall ats Q g,
    (forall g' b,
        (b = true
         -> forall v, rep g {| Values := v |}
                   -> Forall (evalCondition v) ats)
        -> Q g' b)
    -> wpre (checkAll ats) Q g.
Proof.
  induct ats; simplify.

  apply wpre_ret; auto.

  cases a.
  cases Condition0; try (apply wpre_ret; simplify; apply H; equality).
  cases e1; try (apply wpre_ret; simplify; apply H; equality).
  cases e2; try (apply wpre_ret; simplify; apply H; equality).
  cases Value0; try (apply wpre_ret; simplify; apply H; equality).
  apply wpre_bind.
  apply wpre_checkEqual; simplify.
  cases r; try (apply wpre_ret; simplify; apply H; equality).
  propositional.
  apply IHats; simplify.
  cases b; try (apply H; equality).
  propositional.
  apply H; simplify.
  constructor.
  red; simplify.
  rewrite H0 in *.
  apply H1 in H5.
  red in H5.
  simplify.
  rewrite H5.
  cases (v $! x0 ==n v $! x0); equality.
  rewrite H0 in *.
  auto.
Qed.

Lemma entailment_correct : forall ats1 ats2,
    entailment ats1 ats2 = true
    -> forall v, Forall (evalCondition v) ats1
                 -> Forall (fun a => forall x, varInBexp a.(Condition) x
                                               -> v $? x <> None) ats1
                 -> Forall (evalCondition v) ats2.
Proof.
  unfold entailment; simplify.
  assert (wpre (_ <- assertAll ats1; checkAll ats2)
               (fun g b =>
                  b = true
                  -> forall v, Forall (fun a => forall x, varInBexp a.(Condition) x
                                                          -> v $? x <> None) ats1
                               -> Forall (evalCondition v) ats1
                               -> Forall (evalCondition v) ats2)
               empty).

  apply wpre_bind.
  apply wpre_assertAll; simplify.
  apply wpre_checkAll; simplify; propositional.
  apply H7.
  apply H2; auto.
  rewrite rep_empty.
  constructor.
  red in H2.
  cases ((_ <- assertAll ats1; checkAll ats2) empty); simplify; subst.
  specialize (H2 valid_empty); propositional.
  auto.
Qed.  

(* We find ourselves wanting more directly executable ways to find variables
 * appearing in different terms. *)

Fixpoint expVars (e : exp) : list var :=
  match e with
  | Const _ => []
  | Var x => [x]
  | Plus e1 e2 | Minus e1 e2 | Mult e1 e2 => expVars e1 ++ expVars e2
  end.  

Definition bexpVars (e : bexp) : list var :=
  match e with
  | Equal e1 e2 | Less e1 e2 => expVars e1 ++ expVars e2
  end.

Definition atomVars (a : atom) : list var :=
  bexpVars a.(Condition).

(* The following routines make sure certain variables are included in
 * valuations, adding zero mappings for the ones we missed. *)

Definition ensureVar (v : valuation) (x : var) : valuation :=
  match v $? x with
  | None => v $+ (x, 0)
  | Some _ => v
  end.

Fixpoint ensureAtomVars (v : valuation) (ats : list atom) : valuation :=
  match ats with
  | nil => v
  | a :: ats' =>
      let v := fold_left ensureVar (atomVars a) v in
      ensureAtomVars v ats'
  end.

Lemma evalCondition_ensureVar : forall v x a,
    evalCondition (ensureVar v x) a = evalCondition v a.
Proof.
  simplify.
  unfold evalCondition, ensureVar.
  cases (v $? x); auto.
  f_equal.
  apply beval_relevant; simplify.
  cases (x ==v x0); subst; simplify; auto.
  rewrite Heq.
  trivial.
Qed.

Local Hint Resolve evalCondition_ensureVar : core.

Lemma evalCondition_ensureVars : forall a ats v,
    evalCondition (fold_left ensureVar ats v) a = evalCondition v a.
Proof.
  induct ats; simplify; auto.
  rewrite IHats.
  auto.
Qed.

Local Hint Resolve evalCondition_ensureVars : core.

Theorem evalCondition_ensureAtomVars : forall a ats v,
    evalCondition (ensureAtomVars v ats) a = evalCondition v a.
Proof.
  induct ats; simplify; auto.

  rewrite IHats.
  auto.
Qed.

Local Hint Resolve evalCondition_ensureAtomVars : core.

Lemma ensureVars_mono : forall x xs v,
    v $? x <> None
    -> fold_left ensureVar xs v $? x = v $? x.
Proof.
  induct xs; simplify; auto.
  rewrite IHxs.
  unfold ensureVar.
  cases (v $? a); simplify; auto.
  unfold ensureVar.
  cases (v $? a); simplify; auto.
Qed.

Lemma ensureAtomVars_mono : forall x ats v,
    v $? x <> None
    -> ensureAtomVars v ats $? x = v $? x.
Proof.
  induct ats; simplify; auto.
  rewrite IHats.
  apply ensureVars_mono; auto.
  rewrite ensureVars_mono; auto.
Qed.

Local Hint Resolve ensureAtomVars_mono : core.

Local Hint Rewrite fold_left_app.

Lemma ensureVar_fix : forall v x,
    ensureVar v x $? x <> None.
Proof.
  simplify.
  unfold ensureVar.
  cases (v $? x); simplify; equality.
Qed.

Lemma ensureVars_fix : forall x xs v,
    In x xs
    -> fold_left ensureVar xs v $? x <> None.
Proof.
  induct xs; simplify.

  propositional.

  invert H; auto.
  rewrite ensureVars_mono.
  apply ensureVar_fix.
  apply ensureVar_fix.
Qed.

Local Hint Resolve ensureVars_fix : core.

Lemma varInExp_expVars : forall x e,
    varInExp e x
    -> In x (expVars e).
Proof.
  induct e; simplify; propositional; eauto.
Qed.

Local Hint Resolve varInExp_expVars : core.

Lemma varInBexp_bexpVars : forall x e,
    varInBexp e x
    -> In x (bexpVars e).
Proof.
  induct e; simplify; propositional; eauto.
Qed.

Local Hint Resolve varInBexp_bexpVars : core.

Lemma ensureAtomVars_complete : forall ats v,
    Forall (fun a => forall x, varInBexp (Condition a) x
                               -> ensureAtomVars v ats $? x <> None) ats.
Proof.
  induct ats; simplify; constructor; simplify; auto.

  unfold atomVars; auto.
  rewrite ensureAtomVars_mono; eauto.
Qed.

Local Hint Resolve ensureAtomVars_complete : core.

Lemma ensureVar_read : forall v a x,
    ensureVar v a $! x = v $! x.
Proof.
  unfold ensureVar; simplify.
  cases (v $? a); simplify; auto.
  cases (a ==v x); subst; simplify; auto.
  rewrite Heq; trivial.
Qed.

Lemma ensureVars_read : forall x xs v,
    fold_left ensureVar xs v $! x = v $! x.
Proof.
  induct xs; simplify; auto.

  rewrite IHxs.
  apply ensureVar_read.
Qed.

Lemma ensureAtomVars_read : forall x ats v,
    ensureAtomVars v ats $! x = v $! x.
Proof.
  induct ats; simplify; auto.

  rewrite IHats.
  apply ensureVars_read.
Qed.

Local Hint Rewrite ensureAtomVars_read.

(* The big theorem for our first automated verifier!  Sorry for all the side
 * conditions about variable names. *)
Theorem verify_computed : forall pre c post,
    verify_computable pre c post = true
    -> forall v v', evalPredicate pre v
                    -> exec v c v'
                    -> wfPredicate pre
                    -> (forall x n, varInCmd c x \/ varInPredicate pre x \/ varInPredicate post x
                                    -> x <> multibumpVar n "X")
                    -> (forall x, varInCmd c x \/ varInPredicate post x -> In x (boundVars pre) -> False)
                    -> (forall x, In x (boundVars pre) -> v $? x = None)
                    -> (forall n, v $? multibumpVar n "X" = None)
                    -> evalPredicate post v'.
Proof.
  unfold verify_computable; simplify.
  pose proof (fun x => exec_changes x _ _ _ H1) as Hchange.
  cases (scenarios post); try equality.
  cases s.
  cases ExVars0; try equality.
  cases l; try equality.
  eapply scenarios_bwd; eauto.
  eapply spost_sound with (nextVar := "X") in H1; eauto.
  2: first_order.
  eapply scenarios_sound in H1.
  2: apply spost_wf; auto; first_order.
  apply Exists_exists in H1.
  first_order.
  pose proof (proj1 (forallb_forall _ _) H _ H1).
  simplify.
  replace (evalCondition x0) with (evalCondition (ensureAtomVars x0 (Atoms x))) in H9.
  2: apply functional_extensionality; auto.
  eapply entailment_correct in H9; eauto.
  apply Forall_forall; simplify.
  pose proof (proj1 (Forall_forall _ _) H9 _ H11).
  red; red in H12.
  rewrite <- H12.
  apply beval_relevant; simplify.
  cases (v' $? x2).
  eapply includes_lookup in H7; eauto.
  rewrite H7; trivial.
  cases (x0 $? x2); auto.
  assert (In x2 (ExVars x)) by (apply H8; equality).
  specialize (scenarios_dom post).
  rewrite Heq.
  intro Hdom.
  invert Hdom.
  clear H18.
  simplify.
  eapply Forall_forall in H17; eauto.
  apply H17 in H13.
  specialize (scenarios_bound (fst (spost c "X" pre))).
  intro Hbound.
  eapply Forall_forall in Hbound; eauto.
  apply Hbound in H14.
  apply spost_binds in H14.
  invert H14.
  exfalso; eauto.
  invert H15.
  exfalso; eapply H3; eauto.
  
  simplify.
  cases (v' $? x); auto.
  exfalso.
  apply spost_binds in H7.
  first_order; subst.
  assert (varInCmd c x).
  apply Hchange.
  propositional.
  rewrite H5 in H8 by auto.
  equality.
  eauto.
  assert (varInCmd c (multibumpVar x0 "X")).
  apply Hchange.
  propositional.
  rewrite H6 in H7.
  equality.
  eapply H3; eauto.
Qed.

Lemma use_equal : forall a b,
    (if a ==n b then true else false) = true
    -> a = b.
Proof.
  simplify.
  cases (a ==n b); equality.
Qed.

Local Hint Resolve use_equal : core.

(* Let's do an example that is a good fit for showing off this prover. *)

Example ex4 := Seq (Assign "y" (Var "a"))
                   (Seq (If_ (Equal (Var "x") (Var "y"))
                             (Assign "z" (Var "x"))
                             (Assign "z" (Var "y")))
                        (Assign "x" (Var "z"))).
Compute fst (spost ex4 "X" Tru).
(* Yup, plenty of quantifiers and nontrivial structure there! *)

Local Transparent min max.

Theorem ex4_correct : forall v v',
    exec v ex4 v'
    -> (forall n, v $? multibumpVar n "X" = None)
    -> v' $! "x" = v' $! "a".
Proof.
  simplify.
  apply verify_computed with (pre := Tru) (post := Exp (Equal (Var "x") (Var "a"))) in H; simplify; propositional; subst; eauto.

  (* This subgoal is the main action: showing that our checker returns [true].
   * Oh, the suspense! *)
  repeat (compute; simplify).
  reflexivity.
  (* As you can see, outside those annoying variable side conditions, we
   * delegated all the "real work" to our computable procedure. *)
Qed.

(** * TECHNIQUE #2: Symbolic Execution *)

(* Those quantifiers sure are a pain.  A technique often called *symbolic
 * execution* will let us avoid them. *)

(* The main idea is that, while we traverse the program syntax in the forward
 * direction, we maintain a *mapping* of program variables to logical
 * expressions over the *initial* values of variables.  Every predicate we
 * generate will be in terms of those initial values only. *)
Definition mapping := fmap var exp.

(* We must explain how to evaluate different kinds of terms with respect to
 * mappings. *)

Fixpoint expM (e : exp) (m : mapping) : exp :=
  match e with
  | Const _ => e
  | Var x => match m $? x with None => Const 0 | Some e => e end
  | Plus e1 e2 => Plus (expM e1 m) (expM e2 m)
  | Minus e1 e2 => Minus (expM e1 m) (expM e2 m)
  | Mult e1 e2 => Mult (expM e1 m) (expM e2 m)
  end.

Definition bexpM (e : bexp) (m : mapping) : bexp :=
  match e with
  | Equal e1 e2 => Equal (expM e1 m) (expM e2 m)
  | Less e1 e2 => Less (expM e1 m) (expM e2 m)
  end.

Fixpoint predM (p : predicate) (m : mapping) : predicate :=
  match p with
  | Tru | Fals => p
  | Exp e => Exp (bexpM e m)
  | NotExp e => NotExp (bexpM e m)
  | And p1 p2 => And (predM p1 m) (predM p2 m)
  | Or p1 p2 => Or (predM p1 m) (predM p2 m)
  | Ex x p1 => Ex x (predM p1 m)
  end.

(* A classic higher-order function that will come in handy *)
Fixpoint flatmap {A B} (f : A -> list B) (ls : list A) : list B :=
  match ls with
  | nil => nil
  | x :: ls' => f x ++ flatmap f ls'
  end.

(* Now our modified forward-direction program explorer: it takes in a mapping,
 * and it returns *a list of possible control-flow paths*, each with a predicate
 * (called a *path condition* and mapping) to explain state at the end of the
 * path. *)
Fixpoint spostM (c : cmd) (p : predicate) (m : mapping) : list (predicate * mapping) :=
  match c with
  | Skip => [(p, m)]
  | Assign x e => [(p, m $+ (x, expM e m))]
  | Seq c1 c2 =>
      flatmap (fun '(p, m) => spostM c2 p m) (spostM c1 p m)
  | If_ e c1 c2 =>
      spostM c1 (And p (Exp (bexpM e m))) m
      ++ spostM c2 (And p (NotExp (bexpM e m))) m
  end.
(* Note that, every time we extend predicates or mappings, we substitute
 * mappings into terms that will be used.  We maintain the invariant that all
 * logical expressions and predicates are in terms of the *initial* values of
 * variables. *)

(* One more computable version of a useful operation: *)
Fixpoint cmdVars (c : cmd) : list var :=
  match c with
  | Skip => []
  | Assign x e => x :: expVars e
  | Seq c1 c2 => cmdVars c1 ++ cmdVars c2
  | If_ e c1 c2 => bexpVars e ++ cmdVars c1 ++ cmdVars c2
  end.

(* We will use this function to create the mapping at the start of symbolic
 * execution: every program variable contains itself, since there have not been
 * any mutations yet. *)
Fixpoint initMapping (xs : list var) : mapping :=
  match xs with
  | [] => $0
  | x :: xs' => initMapping xs' $+ (x, Var x)
  end.

Definition mappingAgrees (m : mapping) (v0 v : valuation) :=
  forall x, v $! x = match m $? x with
                     | None => 0
                     | Some e => eval e v0
                     end.

Lemma expM_correct : forall v0 v m e,
    mappingAgrees m v0 v
    -> eval e v = eval (expM e m) v0.
Proof.
  induct e; simplify; auto.
  rewrite H.
  cases (m $? x); auto.
Qed.

Lemma bexpM_correct : forall v0 v m e,
    mappingAgrees m v0 v
    -> beval e v = beval (bexpM e m) v0.
Proof.
  induct e; simplify; auto.
  erewrite expM_correct; eauto.
  erewrite expM_correct with (e := e2); eauto.
  erewrite expM_correct; eauto.
  erewrite expM_correct with (e := e1); eauto.
Qed.

Lemma Exists_flatmap : forall A B P P1 (f : A -> list B) ls,
    Exists P1 ls
    -> (forall x, P1 x -> Exists P (f x))
    -> Exists P (flatmap f ls).
Proof.
  induct 1; simplify.

  apply Exists_app; auto.

  apply Exists_app; auto.
Qed.

(* Here's what correctness means for our symbolic executor.  Nice: fewer side
 * conditions about variables!  We just need to mention accuracy of mappings. *)
Theorem spostM_sound : forall v0 v c v',
    exec v c v'
    -> forall m p, evalPredicate p v0
                   -> mappingAgrees m v0 v
                   -> Exists (fun '(p', m') =>
                                evalPredicate p' v0
                                /\ mappingAgrees m' v0 v') (spostM c p m).
Proof.
  induct 1; simplify; auto.

  constructor; propositional.
  red; simplify.
  cases (x ==v x0); subst; simplify.
  apply expM_correct; auto.
  rewrite H0; trivial.

  eapply IHexec1 in H2; eauto; clear IHexec1.
  eapply Exists_flatmap; eauto.
  simplify.
  cases x.
  propositional.
  eauto.

  assert (evalPredicate (And p (Exp (bexpM b m))) v0).
  simplify; propositional.
  erewrite <- bexpM_correct; eauto.
  clear H1.
  eapply IHexec in H2; eauto.
  apply Exists_app; auto.

  assert (evalPredicate (And p (NotExp (bexpM b m))) v0).
  simplify; propositional.
  erewrite <- bexpM_correct; eauto.
  clear H1.
  eapply IHexec in H2; eauto.
  apply Exists_app; auto.
Qed.

(* Let's combine that procedure with the same automated theorem prover we used
 * with strongest postconditions. *)
Definition verifyM_computable (pre : predicate) (c : cmd) (post : predicate) :=
  forallb (fun '(p, m) =>
             match scenarios (predM post m) with
             | [{| ExVars := []; Atoms := apost |}] =>
                 forallb (fun lhs => entailment lhs.(Atoms) apost)
                         (scenarios p)
             | _ => false
             end) (spostM c pre (initMapping (cmdVars c))).
(* Note careful substitution with mappings above. *)

(* Now a moderate journey to prove overall soundness: *)

Lemma initMapping_In : forall x xs,
    In x xs
    -> initMapping xs $? x = Some (Var x).
Proof.
  induct xs; simplify; propositional; subst; simplify; auto.
  cases (x ==v a); subst; simplify; auto.
Qed.

Lemma initMapping_not_In : forall x xs,
    ~In x xs
    -> initMapping xs $? x = None.
Proof.
  induct xs; simplify; propositional; subst; simplify; auto.
Qed.

Lemma mappingAgrees_initMapping : forall v xs,
    (forall x, ~In x xs -> v $? x = None)
    -> mappingAgrees (initMapping xs) v v.
Proof.
  induct xs; simplify.

  red; simplify.
  rewrite H; propositional.

  red; simplify.
  cases (x ==v a); subst; simplify; auto.
  cases (in_dec var_eq x xs).
  rewrite initMapping_In by auto.
  simplify.
  trivial.
  rewrite initMapping_not_In; auto.
  rewrite H; auto.
  equality.
Qed.

Local Hint Resolve mappingAgrees_initMapping : core.

Lemma In_flatmap : forall A B (f : A -> list B) x ls,
    In x (flatmap f ls)
    -> exists y, In y ls /\ In x (f y).
Proof.
  induct ls; simplify; propositional.

  apply in_app_or in H; first_order.
Qed.
  
Lemma spostM_noquant : forall c pre m p m',
    boundVars pre = []
    -> In (p, m') (spostM c pre m)
    -> boundVars p = [].
Proof.
  induct c; simplify; propositional; try equality.

  apply In_flatmap in H0.
  first_order.
  cases x.
  eauto.

  apply in_app_or in H0.
  propositional.
  eapply IHc1; try apply H1.
  simplify.
  assumption.
  eapply IHc2; try apply H1.
  simplify.
  assumption.
Qed.

Lemma noquant_wf : forall p,
    boundVars p = []
    -> wfPredicate p.
Proof.
  induct p; simplify; auto.

  apply app_eq_nil in H; propositional.
  rewrite H0 in H3; simplify; propositional.
  rewrite H1 in H3; simplify; propositional.

  apply app_eq_nil in H; propositional.

  equality.
Qed.  

Local Hint Resolve spostM_noquant noquant_wf : core.

Lemma mappingAgrees_evalPredicate : forall m v' p v,
    mappingAgrees m v v'
    -> evalPredicate (predM p m) v
    -> boundVars p = []
    -> evalPredicate p v'.
Proof.
  induct p; simplify; first_order.

  erewrite <- bexpM_correct in *; eauto.

  erewrite <- bexpM_correct in *; eauto.

  apply app_eq_nil in H1; propositional; eauto.

  apply app_eq_nil in H1; propositional; eauto.

  apply app_eq_nil in H1; propositional; eauto.

  apply app_eq_nil in H1; propositional; eauto.

  equality.
Qed.  

Lemma evalPredicate_ensureAtomVars : forall ats p v,
    evalPredicate p (ensureAtomVars v ats)
    -> evalPredicate p v.
Proof.
  induct p; simplify; first_order.

  rewrite <- H.
  apply beval_relevant; intros.
  symmetry; apply ensureAtomVars_read.

  rewrite <- H.
  apply beval_relevant; intros.
  symmetry; apply ensureAtomVars_read.

  exists x0.
  apply IHp.
  erewrite evalPredicate_relevant; eauto.
  simplify.
  cases (x ==v x1); subst; simplify; auto.
Qed.

(* And here is our new version, again going pretty light on side conditions
 * about variable names. *)
Theorem verifyM_computed : forall pre c post,
    verifyM_computable pre c post = true
    -> forall v v', evalPredicate pre v
                    -> exec v c v'
                    -> boundVars pre = []
                    -> boundVars post = []
                    -> (forall x, ~In x (cmdVars c) -> v $? x = None)
                    -> evalPredicate post v'.
Proof.
  unfold verifyM_computable; simplify.
  eapply spostM_sound with (m := initMapping (cmdVars c)) in H1; eauto.
  apply Exists_exists in H1; first_order.
  cases x; propositional.
  specialize (proj1 (forallb_forall _ _) H _ H1); clear H; simplify.
  cases (scenarios (predM post m)); try equality.
  cases s.
  cases ExVars0; try equality.
  cases l; try equality.
  eapply scenarios_sound in H6; eauto.
  2: erewrite spostM_noquant; try apply H1; eauto.
  apply Exists_exists in H6; first_order.
  eapply forallb_forall in H; eauto.
  replace (evalCondition x0) with (evalCondition (ensureAtomVars x0 (Atoms x))) in H9.
  2: apply functional_extensionality; auto.
  eapply entailment_correct in H9; eauto.
  eapply scenarios_bwd in Heq; eauto.
  eapply mappingAgrees_evalPredicate; eauto.
  apply evalPredicate_ensureAtomVars in Heq.
  erewrite evalPredicate_relevant; eauto.
  intros.
  cases (v $? x1).
  eapply includes_lookup in H6; eauto.
  rewrite H6.
  trivial.
  cases (x0 $? x1); auto.
  assert (In x1 (ExVars x)) by (apply H8; equality).
  specialize (scenarios_bound p); intro Hbound.
  eapply Forall_forall in Hbound; eauto.
  apply Hbound in H11.
  assert (boundVars p = []) by eauto.
  rewrite H12 in H11.
  simplify.
  propositional.
Qed.

Theorem ex4_correctM : forall v v',
    exec v ex4 v'
    -> (forall x, ~In x (cmdVars ex4) -> v $? x = None)
    -> v' $! "x" = v' $! "a".
Proof.
  intros.
  apply verifyM_computed with (pre := Tru) (post := Exp (Equal (Var "x") (Var "a"))) in H; auto; try solve [ simplify; propositional; subst; eauto ].

  repeat (compute; simplify).
  reflexivity.
Qed.

(** * TECHNIQUE #3: Weakest Preconditions *)

(* Our last approach lines up with the weakest preconditions from
 * AutomatedTheoremProving, though now we implement the operation as a
 * computable function on syntactic predicates. *)

Fixpoint wprec (c : cmd) (post : predicate) : predicate :=
  match c with
  | Skip => post
  | Assign x e => subPredicate post x e (* This case is where the magic happens,
                                         * in simplifying vs. strongest
                                         * postconditions. *)
  | Seq c1 c2 => wprec c1 (wprec c2 post)
  | If_ e c1 c2 => Or (And (Exp e) (wprec c1 post))
                      (And (NotExp e) (wprec c2 post))
  end.

(* More lemmas before the main soundness theorems: *)

Lemma eval_subPredicate_noquant : forall replaceThis withThis inThis,
    boundVars inThis = []
    -> forall v, evalPredicate (subPredicate inThis replaceThis withThis) v
                 = evalPredicate inThis (v $+ (replaceThis, eval withThis v)).
Proof.
  induct inThis; simplify; auto.

  apply app_eq_nil in H; propositional.
  rewrite H; eauto.
  rewrite H2; eauto.

  apply app_eq_nil in H; propositional.
  rewrite H; eauto.
  rewrite H2; eauto.

  equality.
Qed.

Lemma wprec_bound : forall c p,
    boundVars p = []
    -> boundVars (wprec c p) = [].
Proof.
  induct c; simplify; auto.
  rewrite IHc1, IHc2; auto.
Qed.

(* Nice simple theorem statement *and* proof here. *)
Theorem wprec_sound : forall v c v',
    exec v c v'
    -> forall post, evalPredicate (wprec c post) v
                    -> boundVars post = []
                    -> evalPredicate post v'.
Proof.
  induct 1; simplify; propositional; eauto; try equality.

  rewrite eval_subPredicate_noquant in H; auto.

  apply IHexec2; auto.
  apply IHexec1; auto.
  apply wprec_bound; auto.
Qed.

(* Simple wrapper into an overall checker for Hoare triples *)
Definition verifyP_computable (pre : predicate) (c : cmd) (post : predicate) :=
  forallb (fun lhs => existsb (fun rhs => entailment lhs.(Atoms) rhs.(Atoms))
                              (scenarios (wprec c post)))
          (scenarios pre).

Lemma In_cross : forall A (f : A -> A -> A) x (ls1 ls2 : list A),
    In x (cross f ls1 ls2)
    -> exists v1 v2, In v1 ls1 /\ In v2 ls2 /\ x = f v1 v2.
Proof.
  induct ls1; simplify; propositional.

  apply in_app_or in H; first_order.
  eapply in_map_iff in H; first_order; subst.
  eauto 6.
Qed.

Lemma scenarios_bwd_multi : forall p ats v,
    In {| ExVars := []; Atoms := ats |} (scenarios p)
    -> List.Forall (evalCondition v) ats
    -> evalPredicate p v.
Proof.
  induct p; simplify; propositional; try equality.

  invert H1.
  invert H0.
  assumption.

  invert H1.
  invert H0.
  assumption.

  apply In_cross in H; first_order.
  invert H2.
  symmetry in H4.
  apply app_eq_nil in H4; propositional.
  cases x; cases x0; simplify; subst.
  apply Forall_app in H0; first_order.

  apply In_cross in H; first_order.
  invert H2.
  symmetry in H4.
  apply app_eq_nil in H4; propositional.
  cases x; cases x0; simplify; subst.
  apply Forall_app in H0; first_order.

  apply in_app_or in H; first_order.

  apply in_map_iff in H; first_order.
  equality.
Qed.

(* Simple side conditions here, too. *)
Theorem verifyP_computed : forall pre c post,
    verifyP_computable pre c post = true
    -> forall v v', evalPredicate pre v
                    -> exec v c v'
                    -> boundVars pre = []
                    -> boundVars post = []
                    -> evalPredicate post v'.
Proof.
  unfold verifyP_computable; simplify.
  eapply wprec_sound; eauto.
  eapply scenarios_sound in H0; eauto.
  2: rewrite H2; simplify; propositional.
  apply Exists_exists in H0; first_order.
  eapply forallb_forall in H; eauto.
  apply existsb_exists in H; first_order.
  cases x1; simplify.
  specialize (scenarios_bound (wprec c post)); intro Hbound.
  eapply Forall_forall in Hbound; eauto; simplify.
  rewrite wprec_bound in Hbound; auto.
  apply incl_l_nil in Hbound; subst.  
  eapply scenarios_bwd_multi; eauto.
  replace (evalCondition x0) with (evalCondition (ensureAtomVars x0 (Atoms x))) in H6.
  2: apply functional_extensionality; auto.  
  eapply entailment_correct in H6; eauto.
  unfold evalCondition in H6; unfold evalCondition.
  apply Forall_forall; intros.
  eapply Forall_forall in H6; eauto.
  rewrite <- H6.
  apply beval_relevant; intros.
  rewrite ensureAtomVars_read.
  cases (v $? x2).
  eapply includes_lookup in H4; eauto.
  rewrite H4.
  trivial.
  cases (x0 $? x2); auto.
  assert (In x2 (ExVars x)) by (apply H5; equality).
  specialize (scenarios_bound pre); intro Hbound.
  eapply Forall_forall in Hbound; eauto.
  apply Hbound in H10.
  rewrite H2 in H10.
  simplify.
  propositional.
Qed.

Lemma use_equal' : forall a b,
    a = b
    -> (if a ==n b then true else false) = true.
Proof.
  simplify.
  cases (a ==n b); equality.
Qed.

Local Hint Resolve use_equal' : core.

(* Note that we need a nontrivial precondition in the following!  Try executing
 * [wprec] on the relevant inputs to see why our automated theorem prover isn't
 * up to the challenge with [Tru] as precondition. *)

Theorem ex4_correctP : forall v v',
    exec v ex4 v'
    -> v $! "x" = v $! "a"
    -> v' $! "x" = v' $! "a".
Proof.
  intros.
  apply verifyP_computed with (pre := Exp (Equal (Var "x") (Var "a"))) (post := Exp (Equal (Var "x") (Var "a"))) in H; try solve [ simplify; auto ].

  repeat (compute; simplify).
  reflexivity.
Qed.
