(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 20: Session Types
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap MessagesAndRefinement.

Set Implicit Arguments.
Set Asymmetric Patterns.


(** * Defining the Type System *)

Inductive type :=
| TSend (ch : channel) (A : Set) (t : type)
| TRecv (ch : channel) (A : Set) (t : type)
| TDone

| InternalChoice (t1 t2 : type)
| ExternalChoice (t1 t2 : type).

Delimit Scope st_scope with st.
Bind Scope st_scope with type.
Notation "!!! ch ( A ) ; k" := (TSend ch A k%st) (right associativity, at level 45, ch at level 0) : st_scope.
Notation "??? ch ( A ) ; k" := (TRecv ch A k%st) (right associativity, at level 45, ch at level 0) : st_scope.
Infix "|?|" := InternalChoice (at level 40) : st_scope.
Infix "?|?" := ExternalChoice (at level 40) : st_scope.

Inductive hasty : proc -> type -> Prop :=
| HtSend : forall ch (A : Set) (v : A) k t,
    hasty k t
    -> hasty (Send ch v k) (TSend ch A t)
| HtRecv : forall ch (A : Set) (k : A -> _) t (v : A),
    (forall v, hasty (k v) t)
    -> hasty (Recv ch k) (TRecv ch A t)
| HtDone :
    hasty Done TDone

| HtInternalChoice1 : forall pr t1 t2,
    hasty pr t1
    -> hasty pr (InternalChoice t1 t2)
| HtInternalChoice2 : forall pr t1 t2,
    hasty pr t2
    -> hasty pr (InternalChoice t1 t2)
| HtExternalChoice : forall pr t1 t2,
    hasty pr t1
    -> hasty pr t2
    -> hasty pr (ExternalChoice t1 t2).


(** * Examples of Typed Processes *)

(* Recall our first example from last chapter. *)
Definition addN (k : nat) (input output : channel) : proc :=
  ??input(n : nat);
  !!output(n + k);
  Done.

Ltac hasty := simplify; repeat (constructor; simplify).

Theorem addN_typed : forall k input output,
    hasty (addN k input output) (???input(nat); !!!output(nat); TDone).
Proof.
  hasty.
Qed.


(** * Complementing Types *)

Fixpoint complement (t : type) : type :=
  match t with
  | TSend ch A t1 => TRecv ch A (complement t1)
  | TRecv ch A t1 => TSend ch A (complement t1)
  | TDone => TDone

  | InternalChoice t1 t2 => ExternalChoice (complement t1) (complement t2)
  | ExternalChoice t1 t2 => InternalChoice (complement t1) (complement t2)
  end.

Definition add2_client (input output : channel) : proc :=
  !!input(42);
  ??output(_ : nat);
  Done.

Theorem add2_client_typed : forall input output,
    input <> output
    -> hasty (add2_client input output) (complement (???input(nat); !!!output(nat); TDone)).
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

Lemma hasty_not_NewChannel : forall chs pr t,
    hasty (NewChannel chs pr) t
    -> False.
Proof.
  induct 1; auto.
Qed.

Lemma hasty_not_BlockChannel : forall ch pr t,
    hasty (BlockChannel ch pr) t
    -> False.
Proof.
  induct 1; auto.
Qed.

Lemma hasty_not_Dup : forall pr t,
    hasty (Dup pr) t
    -> False.
Proof.
  induct 1; auto.
Qed.

Lemma hasty_not_Par : forall pr1 pr2 t,
    hasty (pr1 || pr2) t
    -> False.
Proof.
  induct 1; auto.
Qed.

Hint Immediate hasty_not_NewChannel hasty_not_BlockChannel hasty_not_Dup hasty_not_Par.

Lemma input_typed : forall pr ch A v pr',
    lstep pr (Input {| Channel := ch; TypeOf := A; Value := v |}) pr'
    -> forall t, hasty pr t
                 -> exists k, pr = Recv ch k /\ pr' = k v.
Proof.
  induct 1; simplify; try solve [ exfalso; eauto ].
  induct H; eauto.
Qed.

Lemma output_typed : forall pr ch A v pr',
    lstep pr (Output {| Channel := ch; TypeOf := A; Value := v |}) pr'
    -> forall t, hasty pr t
                 -> exists k, pr = Send ch v k /\ pr' = k.
Proof.
  induct 1; simplify; try solve [ exfalso; eauto ].
  induct H; eauto.
Qed.

Lemma complementarity_rendezvous : forall ch (A : Set) (k1 : A -> _) t,
  hasty (Recv ch k1) t
  -> forall (v : A) k2, hasty (Send ch v k2) (complement t)
    -> exists t', hasty (k1 v) t' /\ hasty k2 (complement t').
Proof.
  induct 1; invert 1; simplify; eauto.
Qed.

Lemma complement_inverse : forall t,
    t = complement (complement t).
Proof.
  induct t; simplify; equality.
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

  invert H6; try solve [ exfalso; eauto ].

  invert H6; try solve [ exfalso; eauto ].

  eapply input_typed in H4; eauto.
  eapply output_typed in H5; eauto.
  first_order; subst.
  eapply complementarity_rendezvous in H0; eauto.
  first_order.

  eapply input_typed in H5; eauto.
  eapply output_typed in H4; eauto.
  first_order; subst.
  rewrite complement_inverse in H0.
  eapply complementarity_rendezvous in H1; eauto.
  first_order.
  rewrite complement_inverse in H.
  first_order.
Qed.

Lemma notstuck_send : forall pr1 t,
    hasty pr1 t
    -> forall pr2, hasty pr2 (complement t)
    -> forall ch (A : Set) (v : A) pr1', lstep pr1 (Output {| Channel := ch; Value := v |}) pr1'
    -> exists pr2', lstep pr2 (Input {| Channel := ch; Value := v |}) pr2'.
Proof.
  induct 1; invert 1; simplify; eauto;
    match goal with
    | [ H : lstep _ _ _ |- _ ] => invert H; eauto
    end.
Qed.

Lemma notstuck_nosilent : forall pr1 t,
    hasty pr1 t
    -> forall pr1', lstep pr1 Silent pr1'
    -> False.
Proof.
  induct 1; invert 1; simplify; eauto.
Qed.

Lemma notstuck_recv : forall pr1 t,
    hasty pr1 t
    -> forall pr2, hasty pr2 (complement t)
    -> forall ch (A : Set) (v : A) pr1', lstep pr1 (Input {| Channel := ch; Value := v |}) pr1'
    -> exists (v' : A) pr2', lstep pr2 (Output {| Channel := ch; Value := v' |}) pr2'.
Proof.
  induct 1; invert 1; simplify; eauto;
    match goal with
    | [ H : lstep _ _ _ |- _ ] => invert H; eauto
    end.
Qed.

Lemma one_thread_progress : forall pr t,
    hasty pr t
    -> pr = Done \/ exists l pr', lstep pr l pr'.
Proof.
  induct 1; first_order; subst; eauto.
  Unshelve.
  assumption.
Qed.

Lemma hasty_Done : forall t,
    hasty Done t
    -> forall pr, hasty pr (complement t)
    -> pr = Done.
Proof.
  induct 1; invert 1; eauto.
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
  simplify; first_order; subst.
  specialize (one_thread_progress H2); first_order; subst.

  eapply hasty_Done in H2; eauto.
  equality.

  cases x2.
  exfalso; eauto using notstuck_nosilent.
  right.
  cases a; cases m.
  eapply notstuck_send in H1; [ | eauto | eauto ].
  first_order; eauto.
  eapply notstuck_recv in H1; [ | eauto | eauto ].
  first_order; eauto.
Qed.
