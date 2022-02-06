(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 5: inductive relations and rule induction
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.


(** * Finite sets as inductive predicates *)

Inductive my_favorite_numbers : nat -> Prop :=
| ILike17 : my_favorite_numbers 17
| ILike23 : my_favorite_numbers 23
| ILike42 : my_favorite_numbers 42.

Check my_favorite_numbers_ind.

Theorem favorites_below_50 : forall n, my_favorite_numbers n -> n < 50.
Proof.
  simplify.
  invert H.
  (* [invert]: case analysis on which rules may have been used to prove an
   *           instance of an inductive predicate *)
  linear_arithmetic.
  linear_arithmetic.
  linear_arithmetic.
Qed.


(** * Transitive closure of relations *)

Inductive tc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TcBase : forall x y, R x y -> tc R x y
| TcTrans : forall x y z, tc R x y -> tc R y z -> tc R x z.

(** ** Less-than reimagined *)

Definition oneApart (n m : nat) : Prop :=
  n + 1 = m.

Definition lt' : nat -> nat -> Prop := tc oneApart.

Theorem lt'_lt : forall n m, lt' n m -> n < m.
Proof.
  induct 1.

  unfold oneApart in H.
  linear_arithmetic.

  linear_arithmetic.
Qed.

Lemma lt'_O_S : forall m, lt' 0 (S m).
Proof.
  induct m; simplify.

  apply TcBase.
  unfold oneApart.
  linear_arithmetic.

  apply TcTrans with (S m).
  assumption.
  apply TcBase.
  unfold oneApart.
  linear_arithmetic.
Qed.

Lemma lt_lt'' : forall n k, lt' n (S k + n).
Proof.
  induct k; simplify.

  apply TcBase.
  unfold oneApart.
  linear_arithmetic.

  apply TcTrans with (S (k + n)).
  assumption.
  apply TcBase.
  unfold oneApart.
  linear_arithmetic.
Qed.
  
Theorem lt_lt' : forall n m, n < m -> lt' n m.
Proof.
  simplify.
  replace m with (S (m - n - 1) + n) by linear_arithmetic.
  (* [replace]: change a subterm into another one, adding an obligation to prove
   *            equality of the two. *)
  apply lt_lt''.
Qed.

(** ** Transitive closure is idempotent. *)

Theorem tc_tc2 : forall A (R : A -> A -> Prop) x y, tc R x y -> tc (tc R) x y.
Proof.
  induct 1.

  apply TcBase.
  apply TcBase.
  assumption.

  apply TcTrans with y.
  assumption.
  assumption.
Qed.

Theorem tc2_tc : forall A (R : A -> A -> Prop) x y, tc (tc R) x y -> tc R x y.
Proof.
  induct 1.

  assumption.

  apply TcTrans with y.
  assumption.
  assumption.
Qed.


(** * Permutation *)

(* Lifted from the Coq standard library: *)
Inductive Permutation {A} : list A -> list A -> Prop :=
| perm_nil :
    Permutation [] []
| perm_skip : forall x l l',
    Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap : forall x y l,
    Permutation (y::x::l) (x::y::l)
| perm_trans : forall l l' l'',
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Lemma Permutation_to_front : forall A (a : A) (ls : list A),
    Permutation (a :: ls) (ls ++ [a]).
Proof.
  induct ls; simplify.

  apply perm_skip.
  apply perm_nil.

  apply perm_trans with (a0 :: a :: ls).
  apply perm_swap.
  apply perm_skip.
  assumption.
Qed.

Theorem Permutation_rev : forall A (ls : list A),
    Permutation ls (rev ls).
Proof.
  induct ls; simplify.

  apply perm_nil.

  apply perm_trans with (a :: rev ls).
  apply perm_skip.
  assumption.
  apply Permutation_to_front.
Qed.

Theorem Permutation_length : forall A (ls1 ls2 : list A),
    Permutation ls1 ls2 -> length ls1 = length ls2.
Proof.
  induct 1; simplify.

  equality.

  equality.

  equality.

  equality.
Qed.

Lemma Permutation_refl : forall A (ls : list A),
    Permutation ls ls.
Proof.
  induct ls.

  apply perm_nil.

  apply perm_skip.
  assumption.
Qed.

Lemma Permutation_app1 : forall A (ls1 ls2 ls : list A),
    Permutation ls1 ls2
    -> Permutation (ls1 ++ ls) (ls2 ++ ls).
Proof.
  induct 1; simplify.

  apply Permutation_refl.

  apply perm_skip.
  apply IHPermutation.

  apply perm_swap.

  apply perm_trans with (l' ++ ls).
  apply IHPermutation1.
  apply IHPermutation2.
Qed.

Lemma Permutation_app2 : forall A (ls ls1 ls2 : list A),
    Permutation ls1 ls2
    -> Permutation (ls ++ ls1) (ls ++ ls2).
Proof.
  induct ls; simplify.

  assumption.

  apply perm_skip.
  apply IHls.
  assumption.
Qed.

Theorem Permutation_app : forall A (ls1 ls1' ls2 ls2' : list A),
    Permutation ls1 ls1'
    -> Permutation ls2 ls2'
    -> Permutation (ls1 ++ ls2) (ls1' ++ ls2').
Proof.
  simplify.
  apply perm_trans with (ls1' ++ ls2).
  apply Permutation_app1.
  assumption.
  apply Permutation_app2.
  assumption.
Qed.


(** * Simple propositional logic *)

Module SimplePropositional.
  Inductive prop :=
  | Truth
  | Falsehood
  | And (p1 p2 : prop)
  | Or (p1 p2 : prop).

  Inductive valid : prop -> Prop :=
  | ValidTruth :
      valid Truth
  | ValidAnd : forall p1 p2,
      valid p1
      -> valid p2
      -> valid (And p1 p2)
  | ValidOr1 : forall p1 p2,
      valid p1
      -> valid (Or p1 p2)
  | ValidOr2 : forall p1 p2,
      valid p2
      -> valid (Or p1 p2).

  Fixpoint interp (p : prop) : Prop :=
    match p with
    | Truth => True
    | Falsehood => False
    | And p1 p2 => interp p1 /\ interp p2
    | Or p1 p2 => interp p1 \/ interp p2
    end.

  Theorem interp_valid : forall p, interp p -> valid p.
  Proof.
    induct p; simplify.

    apply ValidTruth.

    propositional.
    (* [propositional]: simplify goal according to the rules of propositional
     *                  logic, a decidable theory. *)

    propositional.
    apply ValidAnd.
    assumption.
    assumption.

    propositional.
    apply ValidOr1.
    assumption.
    apply ValidOr2.
    assumption.
  Qed.

  Theorem valid_interp : forall p, valid p -> interp p.
  Proof.
    induct 1; simplify.

    propositional.

    propositional.

    propositional.

    propositional.
  Qed.

  Fixpoint commuter (p : prop) : prop :=
    match p with
    | Truth => Truth
    | Falsehood => Falsehood
    | And p1 p2 => And (commuter p2) (commuter p1)
    | Or p1 p2 => Or (commuter p2) (commuter p1)
    end.

  Theorem valid_commuter_fwd : forall p, valid p -> valid (commuter p).
  Proof.
    induct 1; simplify.

    apply ValidTruth.

    apply ValidAnd.
    assumption.
    assumption.

    apply ValidOr2.
    assumption.

    apply ValidOr1.
    assumption.
  Qed.
  
  Theorem valid_commuter_bwd : forall p, valid (commuter p) -> valid p.
  Proof.
    induct p; invert 1; simplify.

    apply ValidTruth.

    apply ValidAnd.
    apply IHp1.
    assumption.
    apply IHp2.
    assumption.

    apply ValidOr2.
    apply IHp2.
    assumption.

    apply ValidOr1.
    apply IHp1.
    assumption.
  Qed.
End SimplePropositional.


(** * Propositional logic with implication *)

Module PropositionalWithImplication.
  Inductive prop :=
  | Truth
  | Falsehood
  | Var (x : var)
  | And (p1 p2 : prop)
  | Or (p1 p2 : prop)
  | Imply (p1 p2 : prop).

  Definition Not (p : prop) := Imply p Falsehood.
  
  Inductive valid (hyps : prop -> Prop) : prop -> Prop :=
  | ValidHyp : forall h,
      hyps h
      -> valid hyps h
  | ValidTruthIntro :
      valid hyps Truth
  | ValidFalsehoodElim : forall p,
      valid hyps Falsehood
      -> valid hyps p
  | ValidAndIntro : forall p1 p2,
      valid hyps p1
      -> valid hyps p2
      -> valid hyps (And p1 p2)
  | ValidAndElim1 : forall p1 p2,
      valid hyps (And p1 p2)
      -> valid hyps p1
  | ValidAndElim2 : forall p1 p2,
      valid hyps (And p1 p2)
      -> valid hyps p2
  | ValidOrIntro1 : forall p1 p2,
      valid hyps p1
      -> valid hyps (Or p1 p2)
  | ValidOrIntro2 : forall p1 p2,
      valid hyps p2
      -> valid hyps (Or p1 p2)
  | ValidOrElim : forall p1 p2 p,
      valid hyps (Or p1 p2)
      -> valid (fun h => h = p1 \/ hyps h) p
      -> valid (fun h => h = p2 \/ hyps h) p
      -> valid hyps p
  | ValidImplyIntro : forall p1 p2,
      valid (fun h => h = p1 \/ hyps h) p2
      -> valid hyps (Imply p1 p2)
  | ValidImplyElim : forall p1 p2,
      valid hyps (Imply p1 p2)
      -> valid hyps p1
      -> valid hyps p2
  | ValidExcludedMiddle : forall p,
      valid hyps (Or p (Not p)).

  Fixpoint interp (vars : var -> Prop) (p : prop) : Prop :=
    match p with
    | Truth => True
    | Falsehood => False
    | Var x => vars x
    | And p1 p2 => interp vars p1 /\ interp vars p2
    | Or p1 p2 => interp vars p1 \/ interp vars p2
    | Imply p1 p2 => interp vars p1 -> interp vars p2
    end.

  Theorem valid_interp : forall vars hyps p,
      valid hyps p
      -> (forall h, hyps h -> interp vars h)
      -> interp vars p.
  Proof.
    induct 1; simplify.

    apply H0.
    assumption.
    
    propositional.

    propositional.
    
    propositional.

    propositional.

    propositional.

    propositional.

    propositional.

    propositional.
    apply IHvalid2.
    propositional.
    equality.
    apply H2.
    assumption.
    apply IHvalid3.
    propositional.
    equality.
    apply H2.
    assumption.

    apply IHvalid.
    propositional.
    equality.
    apply H0.
    assumption.

    propositional.

    excluded_middle (interp vars p); propositional.
    (* Note that use of excluded middle is a bit controversial in Coq,
     * and we'll generally be trying to avoid it,
     * but it helps enough with this example that we don't sweat the details. *)
  Qed.

  Lemma valid_weaken : forall hyps1 p,
      valid hyps1 p
      -> forall hyps2 : prop -> Prop,
        (forall h, hyps1 h -> hyps2 h)
        -> valid hyps2 p.
  Proof.
    induct 1; simplify.

    apply ValidHyp.
    apply H0.
    assumption.

    apply ValidTruthIntro.

    apply ValidFalsehoodElim.
    apply IHvalid.
    assumption.
    
    apply ValidAndIntro.
    apply IHvalid1.
    assumption.
    apply IHvalid2.
    assumption.

    apply ValidAndElim1 with p2.
    apply IHvalid.
    assumption.

    apply ValidAndElim2 with p1.
    apply IHvalid.
    assumption.

    apply ValidOrIntro1.
    apply IHvalid.
    assumption.
  
    apply ValidOrIntro2.
    apply IHvalid.
    assumption.

    apply ValidOrElim with p1 p2.
    apply IHvalid1.
    assumption.
    apply IHvalid2.
    first_order.
    apply IHvalid3.
    first_order.

    apply ValidImplyIntro.
    apply IHvalid.
    propositional.
    right.
    apply H0.
    assumption.

    apply ValidImplyElim with p1.
    apply IHvalid1.
    assumption.
    apply IHvalid2.
    assumption.

    apply ValidExcludedMiddle.
  Qed.

  Lemma valid_cut : forall hyps1 p p',
      valid hyps1 p
      -> forall hyps2, valid hyps2 p'
                       -> (forall h, hyps1 h -> hyps2 h \/ h = p')
                       -> valid hyps2 p.
  Proof.
    induct 1; simplify.

    apply H1 in H.
    propositional.
    apply ValidHyp.
    assumption.
    equality.
    
    apply ValidTruthIntro.

    apply ValidFalsehoodElim.
    apply IHvalid; assumption.

    apply ValidAndIntro.
    apply IHvalid1; assumption.
    apply IHvalid2; assumption.

    apply ValidAndElim1 with p2.
    apply IHvalid; assumption.
    
    apply ValidAndElim2 with p1.
    apply IHvalid; assumption.
    
    apply ValidOrIntro1.
    apply IHvalid; assumption.

    apply ValidOrIntro2.
    apply IHvalid; assumption.

    apply ValidOrElim with p1 p2.
    apply IHvalid1; assumption.
    apply IHvalid2.
    apply valid_weaken with hyps2.
    assumption.
    propositional.
    first_order.
    apply IHvalid3.
    apply valid_weaken with hyps2.
    assumption.
    propositional.
    first_order.
    
    apply ValidImplyIntro.
    apply IHvalid.
    apply valid_weaken with hyps2.
    assumption.
    propositional.
    first_order.

    apply ValidImplyElim with p1.
    apply IHvalid1; assumption.
    apply IHvalid2; assumption.

    apply ValidExcludedMiddle.
  Qed.

  Fixpoint varsOf (p : prop) : list var :=
    match p with
    | Truth
    | Falsehood => []
    | Var x => [x]
    | And p1 p2
    | Or p1 p2
    | Imply p1 p2 => varsOf p1 ++ varsOf p2
    end.

  Lemma interp_valid'' : forall p hyps,
      (forall x, In x (varsOf p) -> hyps (Var x) \/ hyps (Not (Var x)))
      -> (forall x, hyps (Var x) -> ~hyps (Not (Var x)))
      -> IFF interp (fun x => hyps (Var x)) p
         then valid hyps p
         else valid hyps (Not p).
  Proof.
    induct p; unfold IF_then_else; simplify.

    left; propositional.
    apply ValidTruthIntro.

    right; propositional.
    apply ValidImplyIntro.
    apply ValidHyp.
    propositional.

    specialize (H x); propositional.
    left; propositional.
    apply ValidHyp.
    assumption.
    right; first_order.
    apply ValidHyp.
    assumption.

    excluded_middle (interp (fun x => hyps (Var x)) p1).
    excluded_middle (interp (fun x => hyps (Var x)) p2).
    left; propositional.
    apply ValidAndIntro.
    assert (IFF interp (fun x : var => hyps (Var x)) p1 then valid hyps p1 else valid hyps (Not p1)).
    apply IHp1; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H3; propositional.
    assert (IFF interp (fun x : var => hyps (Var x)) p2 then valid hyps p2 else valid hyps (Not p2)).
    apply IHp2; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H3; propositional.
    right; propositional.
    assert (IFF interp (fun x : var => hyps (Var x)) p2 then valid hyps p2 else valid hyps (Not p2)).
    apply IHp2; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H3; propositional.
    apply ValidImplyIntro.
    apply ValidImplyElim with p2.
    apply valid_weaken with hyps.
    assumption.
    propositional.
    apply ValidAndElim2 with p1.
    apply ValidHyp.
    propositional.
    right; propositional.
    assert (IFF interp (fun x : var => hyps (Var x)) p1 then valid hyps p1 else valid hyps (Not p1)).
    apply IHp1; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H2; propositional.
    apply ValidImplyIntro.
    apply ValidImplyElim with p1.
    apply valid_weaken with hyps.
    assumption.
    propositional.
    apply ValidAndElim1 with p2.
    apply ValidHyp.
    propositional.

    excluded_middle (interp (fun x => hyps (Var x)) p1).
    left; propositional.
    apply ValidOrIntro1.
    assert (IFF interp (fun x : var => hyps (Var x)) p1 then valid hyps p1 else valid hyps (Not p1)).
    apply IHp1; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H2; propositional.
    excluded_middle (interp (fun x => hyps (Var x)) p2).
    left; propositional.
    apply ValidOrIntro2.
    assert (IFF interp (fun x : var => hyps (Var x)) p2 then valid hyps p2 else valid hyps (Not p2)).
    apply IHp2; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H3; propositional.
    right; propositional.
    apply ValidImplyIntro.
    apply ValidOrElim with p1 p2.
    apply ValidHyp.
    propositional.
    assert (IFF interp (fun x : var => hyps (Var x)) p1 then valid hyps p1 else valid hyps (Not p1)).
    apply IHp1; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H3; propositional.
    apply ValidImplyElim with p1.
    apply valid_weaken with hyps.
    assumption.
    propositional.
    apply ValidHyp.
    propositional.
    assert (IFF interp (fun x : var => hyps (Var x)) p2 then valid hyps p2 else valid hyps (Not p2)).
    apply IHp2; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H3; propositional.
    apply ValidImplyElim with p2.
    apply valid_weaken with hyps.
    assumption.
    propositional.
    apply ValidHyp.
    propositional.
    
    excluded_middle (interp (fun x => hyps (Var x)) p1).
    excluded_middle (interp (fun x => hyps (Var x)) p2).
    left; propositional.
    apply ValidImplyIntro.
    assert (IFF interp (fun x : var => hyps (Var x)) p2 then valid hyps p2 else valid hyps (Not p2)).
    apply IHp2; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H3; propositional.
    apply valid_weaken with hyps.
    assumption.
    propositional.
    right; propositional.
    apply ValidImplyIntro.
    assert (IFF interp (fun x : var => hyps (Var x)) p1 then valid hyps p1 else valid hyps (Not p1)).
    apply IHp1; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H3; propositional.
    assert (IFF interp (fun x : var => hyps (Var x)) p2 then valid hyps p2 else valid hyps (Not p2)).
    apply IHp2; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H4; propositional.
    apply ValidImplyElim with p2.
    apply valid_weaken with hyps.
    assumption.
    propositional.
    apply ValidImplyElim with p1.
    apply ValidHyp.
    propositional.
    apply valid_weaken with hyps.
    assumption.
    propositional.
    left; propositional.
    apply ValidImplyIntro.
    assert (IFF interp (fun x : var => hyps (Var x)) p1 then valid hyps p1 else valid hyps (Not p1)).
    apply IHp1; propositional.
    apply H.
    apply in_or_app; propositional.
    unfold IF_then_else in H2; propositional.
    apply ValidFalsehoodElim.
    apply ValidImplyElim with p1.
    apply valid_weaken with hyps.
    assumption.
    propositional.
    apply ValidHyp.
    propositional.
  Qed.
  
  Lemma interp_valid' : forall p leftToDo alreadySplit,
      (forall x, In x (varsOf p) -> In x (alreadySplit ++ leftToDo))
      -> forall hyps, (forall x, In x alreadySplit -> hyps (Var x) \/ hyps (Not (Var x)))
      -> (forall x, hyps (Var x) \/ hyps (Not (Var x)) -> In x alreadySplit)
      -> (forall x, hyps (Var x) -> ~hyps (Not (Var x)))
      -> (forall vars : var -> Prop,
             (forall x, hyps (Var x) -> vars x)
             -> (forall x, hyps (Not (Var x)) -> ~vars x)
             -> interp vars p)
      -> valid hyps p.
  Proof.
    induct leftToDo; simplify.

    rewrite app_nil_r in H.
    assert (IFF interp (fun x : var => hyps (Var x)) p then valid hyps p else valid hyps (Not p)).
    apply interp_valid''; first_order.
    unfold IF_then_else in H4; propositional.
    exfalso.
    apply H4.
    apply H3.
    propositional.
    first_order.

    excluded_middle (In a alreadySplit).

    apply IHleftToDo with alreadySplit; simplify.
    apply H in H5.
    apply in_app_or in H5.
    simplify.
    apply in_or_app.
    propositional; subst.
    propositional.
    first_order.
    first_order.
    first_order.
    first_order.

    apply ValidOrElim with (Var a) (Not (Var a)).
    apply ValidExcludedMiddle.

    apply IHleftToDo with (alreadySplit ++ [a]); simplify.
    apply H in H5.
    apply in_app_or in H5.
    simplify.
    apply in_or_app.
    propositional; subst.
    left; apply in_or_app; propositional.
    left; apply in_or_app; simplify; propositional.
    apply in_app_or in H5.
    simplify.
    propositional; subst.
    apply H0 in H6.
    propositional.
    propositional.
    propositional.
    invert H5.
    apply in_or_app.
    simplify.
    propositional.
    apply in_or_app.
    simplify.
    first_order.
    invert H5.
    apply in_or_app.
    simplify.
    first_order.
    propositional.
    invert H5.
    invert H7.
    first_order.
    invert H5.
    first_order.
    apply H3.
    first_order.
    first_order.

    apply IHleftToDo with (alreadySplit ++ [a]); simplify.
    apply H in H5.
    apply in_app_or in H5.
    simplify.
    apply in_or_app.
    propositional; subst.
    left; apply in_or_app; propositional.
    left; apply in_or_app; simplify; propositional.
    apply in_app_or in H5.
    simplify.
    propositional; subst.
    apply H0 in H6.
    propositional.
    propositional.
    propositional.
    invert H5.
    apply in_or_app.
    simplify.
    first_order.
    invert H5.
    apply in_or_app.
    simplify.
    propositional.
    apply in_or_app.
    simplify.
    first_order.
    propositional.
    invert H7.
    invert H7.
    invert H5.
    first_order.
    first_order.
    apply H3.
    first_order.
    first_order.
  Qed.
    
  Theorem interp_valid : forall p,
      (forall vars, interp vars p)
      -> valid (fun _ => False) p.
  Proof.
    simplify.
    apply interp_valid' with (varsOf p) []; simplify; first_order.
  Qed.
End PropositionalWithImplication.
