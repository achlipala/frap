(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 20: Session Types
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap FunctionalExtensionality MessagesAndRefinement.

Set Implicit Arguments.
Set Asymmetric Patterns.


(** * Defining the Type System *)

Inductive type :=
| TSend (ch : channel) (A : Set) (t : A -> type)
| TRecv (ch : channel) (A : Set) (t : A -> type)
| TDone.

Delimit Scope st_scope with st.
Bind Scope st_scope with type.
Notation "!!! ch ( x : A ) ; k" := (TSend ch (fun x : A => k)%st) (right associativity, at level 45, ch at level 0, x at level 0) : st_scope.
Notation "??? ch ( x : A ) ; k" := (TRecv ch (fun x : A => k)%st) (right associativity, at level 45, ch at level 0, x at level 0) : st_scope.

Inductive hasty : proc -> type -> Prop :=
| HtSend : forall ch (A : Set) (v : A) k t,
    hasty k (t v)
    -> hasty (Send ch v k) (TSend ch t)
| HtRecv : forall ch (A : Set) (k : A -> _) t,
    (forall v, hasty (k v) (t v))
    -> hasty (Recv ch k) (TRecv ch t)
| HtDone :
    hasty Done TDone.


(** * Examples of Typed Processes *)

(* Recall our first example from last chapter. *)
Definition addN (k : nat) (input output : channel) : proc :=
  ??input(n : nat);
  !!output(n + k);
  Done.

Ltac hasty := simplify; repeat (constructor; simplify).

Theorem addN_typed : forall k input output,
    hasty (addN k input output) (???input(_ : nat); !!!output(_ : nat); TDone).
Proof.
  hasty.
Qed.


(** * Complementing Types *)

Fixpoint complement (t : type) : type :=
  match t with
  | TSend ch _ t1 => TRecv ch (fun v => complement (t1 v))
  | TRecv ch _ t1 => TSend ch (fun v => complement (t1 v))
  | TDone => TDone
  end.

Definition add2_client (input output : channel) : proc :=
  !!input(42);
  ??output(_ : nat);
  Done.

Theorem add2_client_typed : forall input output,
    hasty (add2_client input output) (complement (???input(_ : nat); !!!output(_ : nat); TDone)).
Proof.
  hasty.
Qed.


(** * Parallel execution preserves the existence of complementary session types. *)

Definition trsys_of pr := {|
  Initial := {pr};
  Step := lstepSilent
|}.
(* Note: here we force silent steps, so that all channel communication is
 * internal. *)

Hint Constructors hasty.

Lemma input_typed : forall pr ch A v pr',
    lstep pr (Input {| Channel := ch; TypeOf := A; Value := v |}) pr'
    -> forall t, hasty pr t
                 -> exists k, pr = Recv ch k /\ pr' = k v.
Proof.
  induct 1; invert 1; eauto.
Qed.

Lemma output_typed : forall pr ch A v pr',
    lstep pr (Output {| Channel := ch; TypeOf := A; Value := v |}) pr'
    -> forall t, hasty pr t
                 -> exists k, pr = Send ch v k /\ pr' = k.
Proof.
  induct 1; invert 1; eauto.
Qed.

Lemma complementarity_forever : forall pr1 pr2 t,
    hasty pr1 t
    -> hasty pr2 (complement t)
    -> invariantFor (trsys_of (pr1 || pr2))
                    (fun pr => exists pr1' pr2' t',
                         pr = pr1' || pr2'
                         /\ hasty pr1' t'
                         /\ hasty pr2' (complement t')).
Proof.
  simplify.
  apply invariant_induction; simplify.

  propositional; subst.
  eauto 6.

  clear pr1 pr2 t H H0.
  first_order; subst.
  invert H2.

  invert H6; invert H0.
  invert H6; invert H1.
  eapply input_typed in H4; eauto.
  eapply output_typed in H5; eauto.
  first_order; subst.
  invert H0.
  invert H1.
  eauto 7.
  eapply input_typed in H5; eauto.
  eapply output_typed in H4; eauto.
  first_order; subst.
  invert H0.
  invert H1.
  eauto 10.
Qed.

Theorem no_deadlock : forall pr1 pr2 t,
    hasty pr1 t
    -> hasty pr2 (complement t)
    -> invariantFor (trsys_of (pr1 || pr2))
                    (fun pr => pr = (Done || Done)
                               \/ exists l' pr', lstep pr l' pr').
Proof.
  simplify.
  eapply invariant_weaken.
  eapply complementarity_forever; eauto.

  clear pr1 pr2 t H H0.
  simplify; first_order; subst.
  invert H0; invert H1; simplify; eauto.
  Unshelve.
  assumption.
Qed.
