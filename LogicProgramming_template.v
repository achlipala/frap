(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Supplementary Rocq material: unification and logic programming
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/
  * Much of the material comes from CPDT <http://adam.chlipala.net/cpdt/> by the same author. *)

Require Import Frap.

Set Implicit Arguments.


(** * Introducing Logic Programming *)

(* Recall the definition of addition from the standard library. *)

Definition real_plus := Eval compute in plus.
Print real_plus.

(* Alternatively, we can define it as a relation. *)

Inductive plusR : nat -> nat -> nat -> Prop :=
| PlusO : forall m, plusR O m m
| PlusS : forall n m r, plusR n m r
  -> plusR (S n) m (S r).

(* Let's prove the correspondence. *)

Theorem plusR_plus : forall n m r,
  plusR n m r
  -> r = n + m.
Proof.
Admitted.

Theorem plus_plusR : forall n m,
  plusR n m (n + m).
Proof.
Admitted.

Example four_plus_three : 4 + 3 = 7.
Proof.
  reflexivity.
Qed.

Print four_plus_three.

Example four_plus_three' : plusR 4 3 7.
Proof.
Admitted.

Print four_plus_three'.

Example five_plus_three : plusR 5 3 8.
Proof.
Admitted.

(* Demonstrating _backtracking_ *)
Example seven_minus_three : exists x, x + 3 = 7.
Proof.
  apply ex_intro with 0.
Abort.

Example seven_minus_three' : exists x, plusR x 3 7.
Proof.
Admitted.

(* Backwards! *)
Example seven_minus_four' : exists x, plusR 4 x 7.
Proof.
Admitted.

Example seven_minus_three'' : exists x, x + 3 = 7.
Proof.
Admitted.

Example seven_minus_four : exists x, 4 + x = 7.
Proof.
Admitted.

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
Proof.
Admitted.

Check eq_trans.

Section slow.
  Hint Resolve eq_trans : core.

  Example zero_minus_one : exists x, 1 + x = 0.
    Time eauto 1.
    Time eauto 2.
    Time eauto 3.
    Time eauto 4.
    Time eauto 5.

    debug eauto 3.
  Abort.
End slow.

Example from_one_to_zero : exists x, 1 + x = 0.
Proof.
Admitted.

Example seven_minus_three_again : exists x, x + 3 = 7.
Proof.
Admitted.

Example needs_trans : forall x y, 1 + x = y
  -> y = 2
  -> exists z, z + x = 3.
Proof.
Admitted.


(** * Searching for Underconstrained Values *)

Print Datatypes.length.

Example length_1_2 : length (1 :: 2 :: nil) = 2.
Proof.
Admitted.

Print length_1_2.

Example length_is_2 : exists ls : list nat, length ls = 2.
Proof.
Abort.

Print Forall.

Example length_is_2 : exists ls : list nat, length ls = 2
  /\ Forall (fun n => n >= 1) ls.
Proof.
Admitted.

Print length_is_2.

Definition sum := fold_right plus O.

Example length_and_sum : exists ls : list nat, length ls = 2
  /\ sum ls = O.
Proof.
Admitted.

Print length_and_sum.

Example length_and_sum' : exists ls : list nat, length ls = 5
  /\ sum ls = 42.
Proof.
Admitted.

Print length_and_sum'.

Example length_and_sum'' : exists ls : list nat, length ls = 2
  /\ sum ls = 3
  /\ Forall (fun n => n <> 0) ls.
Proof.
Admitted.

Print length_and_sum''.


(** * Synthesizing Programs *)

Inductive exp : Set :=
| Const (n : nat)
| Var
| Plus (e1 e2 : exp).

Inductive eval (var : nat) : exp -> nat -> Prop :=
| EvalConst : forall n, eval var (Const n) n
| EvalVar : eval var Var var
| EvalPlus : forall e1 e2 n1 n2, eval var e1 n1
  -> eval var e2 n2
  -> eval var (Plus e1 e2) (n1 + n2).

Local Hint Constructors eval : core.

Example eval1 : forall var, eval var (Plus Var (Plus (Const 8) Var)) (var + (8 + var)).
Proof.
  auto.
Qed.

Example eval1' : forall var, eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8).
Proof.
  eauto.
Abort.

Example eval1' : forall var, eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8).
Proof.
Admitted.

Example synthesize1 : exists e, forall var, eval var e (var + 7).
Proof.
Admitted.

Print synthesize1.

(* Here are two more examples showing off our program-synthesis abilities. *)

Example synthesize2 : exists e, forall var, eval var e (2 * var + 8).
Proof.
Admitted.

Print synthesize2.

Example synthesize3 : exists e, forall var, eval var e (3 * var + 42).
Proof.
Admitted.

Print synthesize3.

Theorem linear : forall e, exists k n,
  forall var, eval var e (k * var + n).
Proof.
Admitted.

Section side_effect_sideshow.
  Variable A : Set.
  Variables P Q : A -> Prop.
  Variable x : A.

  Hypothesis Px : P x.
  Hypothesis Qx : Q x.

  Theorem double_threat : exists y, P y /\ Q y.
  Proof.
    eexists; propositional.
    eauto.
    eauto.
  Qed.
End side_effect_sideshow.


(** * More on [auto] Hints *)

Theorem bool_neq : true <> false.
Proof.
Admitted.

Section forall_and.
  Variable A : Set.
  Variables P Q : A -> Prop.

  Hypothesis both : forall x, P x /\ Q x.

  Theorem forall_and : forall z, P z.
  Proof.
  Admitted.
End forall_and.


(** * Rewrite Hints *)

Section autorewrite.
  Variable A : Set.
  Variable f : A -> A.

  Hypothesis f_f : forall x, f (f x) = f x.

  Hint Rewrite f_f.

  Lemma f_f_f : forall x, f (f (f x)) = f x.
  Proof.
    intros; autorewrite with core; reflexivity.
  Qed.

  Section garden_path.
    Variable g : A -> A.
    Hypothesis f_g : forall x, f x = g x.
    Hint Rewrite f_g.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
    Proof.
    Admitted.
  End garden_path.

  Lemma in_star : forall x y, f (f (f (f x))) = f (f y)
    -> f x = f (f (f y)).
  Proof.
  Admitted.

End autorewrite.
