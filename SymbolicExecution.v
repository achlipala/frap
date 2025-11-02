Require Import Frap.
From Stdlib Require Import FunctionalExtensionality.

(* Let's make a reduced copy of our language from the HoareLogic chapter. *)

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
 * will use in program specifications. *)

Inductive predicate :=
| Exp (e : bexp)
| Not (p1 : predicate)
| And (p1 p2 : predicate)
| Or (p1 p2 : predicate)
| Ex (x : var) (p1 : predicate).

Fixpoint evalPredicate (p : predicate) (v : valuation) : Prop :=
  match p with
  | Exp e => beval e v = true
  | Not p1 => ~evalPredicate p1 v
  | And p1 p2 => evalPredicate p1 v /\ evalPredicate p2 v
  | Or p1 p2 => evalPredicate p1 v \/ evalPredicate p2 v
  | Ex x p1 => exists xv, evalPredicate p1 (v $+ (x, xv))
  end.

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
  | Exp e => Exp (subBexp e replaceThis withThis)
  | Not p => Not (subPredicate p replaceThis withThis)
  | And p1 p2 => And (subPredicate p1 replaceThis withThis) (subPredicate p2 replaceThis withThis)
  | Or p1 p2 => Or (subPredicate p1 replaceThis withThis) (subPredicate p2 replaceThis withThis)
  | Ex x p1 => if x ==v replaceThis then
                 inThis
               else
                 Ex x (subPredicate p1 replaceThis withThis)
  end.

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
  | Exp e => varInBexp e x
  | Not p1 => varInPredicate p1 x
  | And p1 p2 | Or p1 p2 => varInPredicate p1 x \/ varInPredicate p2 x
  | Ex y p1 => y = x \/ varInPredicate p1 x
  end.

Definition bumpVar (x : string) : string := x ++ "'".
Fixpoint multibumpVar (n : nat) (x : string) : string :=
  match n with
  | O => x
  | S n' => bumpVar (multibumpVar n' x)
  end.

Fixpoint spost (c : cmd) (nextVar : var) (p : predicate) : predicate * var :=
  match c with
  | Skip => (p, nextVar)
  | Assign x e => (Ex nextVar (And (subPredicate p x (Var nextVar)) (Exp (Equal (Var x) (subExp e x (Var nextVar))))), bumpVar nextVar)
  | Seq c1 c2 =>
      let (p, nextVar) := spost c1 nextVar p in
      spost c2 nextVar p
  | If_ e c1 c2 =>
      let (p1, nextVar) := spost c1 nextVar (And p (Exp e)) in
      let (p2, nextVar) := spost c2 nextVar (And p (Not (Exp e))) in
      (Or p1 p2, nextVar)
  end.

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

  rewrite IHinThis; auto.

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
  specialize (IHc2 (multibumpVar x nextVar) (And p (Not (Exp be)))).
  cases (spost c2 (multibumpVar x nextVar) (And p (Not (Exp be)))).
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
  specialize (IHc2 s (And p (Not (Exp be)))).
  cases (spost c2 s (And p (Not (Exp be)))).
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

Theorem spost_sound : forall v c v',
    exec v c v'
    -> forall nextVar p, evalPredicate p v
                         -> (forall x n, varInCmd c x \/ varInPredicate p x
                                         -> x <> multibumpVar n nextVar)
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
  cases (spost c2 s (And p (Not (Exp b)))).
  simplify.
  left.
  apply IHexec; propositional; subst; eauto.

  cases (spost c1 nextVar (And p (Exp b))).
  specialize (IHexec s (And p (Not (Exp b)))).
  cases (spost c2 s (And p (Not (Exp b)))).
  simplify.
  right.
  apply spost_bumps in Heq; invert Heq.
  apply IHexec; propositional; subst; simplify; eauto; equality.
Qed.
