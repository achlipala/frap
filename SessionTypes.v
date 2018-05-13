(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 20: Session Types
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap FunctionalExtensionality MessagesAndRefinement.

Set Implicit Arguments.
Set Asymmetric Patterns.


(** * Two-Party Session Types *)

Module TwoParty.

(** ** Defining the type system *)

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


(** * Examples of typed processes *)

(* Recall our first example from last chapter. *)
Definition addN (k : nat) (input output : channel) : proc :=
  ??input(n : nat);
  !!output(n + k);
  Done.

Ltac hasty := simplify; repeat ((constructor; simplify)
                                || match goal with
                                   | [ |- hasty _ (match ?E with _ => _ end) ] => cases E
                                   | [ |- hasty (match ?E with _ => _ end) _ ] => cases E
                                   end).

Theorem addN_typed : forall k input output,
    hasty (addN k input output) (???input(_ : nat); !!!output(_ : nat); TDone).
Proof.
  hasty.
Qed.


(** * Complementing types *)

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

(** ** Example *)

Section online_store.
  Variables request_product in_stock_or_not send_payment_info payment_success add_review : channel.

  Definition customer (product payment_info : string) :=
    !!request_product(product);
    ??in_stock_or_not(worked : bool);
    if worked then
      !!send_payment_info(payment_info);
      ??payment_success(worked_again : bool);
      if worked_again then
        !!add_review((product, "awesome"));
        Done
      else
        Done
    else
      Done.

  Definition customer_type :=
    (!!!request_product(_ : string);
     ???in_stock_or_not(worked : bool);
     if worked then
       !!!send_payment_info(_ : string);
       ???payment_success(worked_again : bool);
       if worked_again then
         !!!add_review(_ : (string * string)%type);
         TDone
       else
         TDone
     else
       TDone)%st.

  Theorem customer_hasty : forall product payment_info,
      hasty (customer product payment_info) customer_type.
  Proof.
    hasty.
  Qed.

  Definition merchant (in_stock payment_checker : string -> bool) :=
    ??request_product(product : string);
    if in_stock product then
      !!in_stock_or_not(true);
      ??send_payment_info(payment_info : string);
      if payment_checker payment_info then
        !!payment_success(true);
        ??add_review(_ : (string * string)%type);
        Done
      else
        !!payment_success(false);
        Done
    else
      !!in_stock_or_not(false);
      Done.

  Theorem merchant_hasty : forall in_stock payment_checker,
      hasty (merchant in_stock payment_checker) (complement customer_type).
  Proof.
    hasty.
  Qed.
End online_store.


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

Example online_store_no_deadlock : forall request_product in_stock_or_not
                                          send_payment_info payment_success add_review
                                          product payment_info in_stock payment_checker,
  invariantFor (trsys_of (customer request_product in_stock_or_not
                                   send_payment_info payment_success add_review
                                   product payment_info
                          || merchant request_product in_stock_or_not
                                      send_payment_info payment_success add_review
                                      in_stock payment_checker))
               (fun pr => pr = (Done || Done)
                          \/ exists l' pr', lstep pr l' pr').
Proof.
  simplify.
  eapply no_deadlock with (t := customer_type request_product in_stock_or_not
                                              send_payment_info payment_success add_review);
    hasty.
Qed.

End TwoParty.


(** * Multiparty Session Types *)

Module Multiparty.

(** ** Defining the type system *)

Inductive type :=
| Communicate (ch : channel) (A : Set) (t : A -> type)
| TDone.

Delimit Scope st_scope with st.
Bind Scope st_scope with type.
Notation "!!! ch ( x : A ) ; k" := (Communicate ch (fun x : A => k)%st) (right associativity, at level 45, ch at level 0, x at level 0) : st_scope.

Section parties.
  Variable party : Set.

  Record parties := {
    Sender : party;
    Receiver : party
  }.

  Variable channels : channel -> parties.

  Inductive hasty (p : party) : bool -> proc -> type -> Prop :=
  | HtSend : forall ch rr (A : Set) (v : A) k t,
    channels ch = {| Sender := p; Receiver := rr |}
    -> rr <> p
    -> hasty p false k (t v)
    -> hasty p false (Send ch v k) (Communicate ch t)
  | HtRecv : forall mayNotSend ch sr (A : Set) (k : A -> _) t (witness : A),
      channels ch = {| Sender := sr; Receiver := p |}
      -> sr <> p
      -> (forall v, hasty p false (k v) (t v))
      -> hasty p mayNotSend (Recv ch k) (Communicate ch t)
  | HtSkip : forall mayNotSend ch sr rr (A : Set) pr (t : A -> _) (witness : A),
      channels ch = {| Sender := sr; Receiver := rr |}
      -> sr <> p
      -> rr <> p
      -> (forall v, hasty p true pr (t v))
      -> hasty p mayNotSend pr (Communicate ch t)
  | HtDone : forall mayNotSend,
      hasty p mayNotSend Done TDone.
End parties.


(** * Parallel execution preserves the existence of complementary session types. *)

Definition trsys_of pr := {|
  Initial := {pr};
  Step := lstepSilent
|}.

Hint Constructors hasty.

Lemma hasty_not_Block : forall party (channels: _ -> parties party) p mns ch pr t,
    hasty channels p mns (BlockChannel ch pr) t
    -> False.
Proof.
  induct 1; auto.
  Unshelve.
  assumption.
Qed.

Lemma hasty_not_Dup : forall party (channels: _ -> parties party) p mns pr t,
    hasty channels p mns (Dup pr) t
    -> False.
Proof.
  induct 1; auto.
  Unshelve.
  assumption.
Qed.

Lemma hasty_not_Par : forall party (channels: _ -> parties party) p mns pr1 pr2 t,
    hasty channels p mns (pr1 || pr2) t
    -> False.
Proof.
  induct 1; auto.
  Unshelve.
  assumption.
Qed.

Hint Immediate hasty_not_Block hasty_not_Dup hasty_not_Par.

Lemma input_typed' : forall party (channels : _ -> parties party) p mns ch (A : Set) (k : A -> _) t,
    hasty channels p mns (Recv ch k) t
    -> exists sr (witness : A), channels ch = {| Sender := sr; Receiver := p |}
                                /\ sr <> p.
Proof.
  induct 1; eauto.
  Unshelve.
  assumption.
Qed.

Lemma input_typed : forall party (channels: _ -> parties party) pr ch A v pr',
    lstep pr (Input {| Channel := ch; TypeOf := A; Value := v |}) pr'
    -> forall p mns t, hasty channels p mns pr t
                       -> exists sr k, pr = Recv ch k /\ pr' = k v
                                       /\ channels ch = {| Sender := sr; Receiver := p |}
                                       /\ sr <> p.
Proof.
  induct 1; simplify; try solve [ exfalso; eauto ].
  eapply input_typed' in H.
  first_order.
  eauto 6.
Qed.

Lemma output_typed' : forall party (channels : _ -> parties party) p mns ch (A : Set) (v : A) k t,
    hasty channels p mns (Send ch v k) t
    -> exists rr, channels ch = {| Sender := p; Receiver := rr |}
                  /\ rr <> p.
Proof.
  induct 1; eauto.
  Unshelve.
  assumption.
Qed.

Lemma output_typed : forall party (channels: _ -> parties party) pr ch A v pr',
    lstep pr (Output {| Channel := ch; TypeOf := A; Value := v |}) pr'
    -> forall p mns t, hasty channels p mns pr t
                       -> exists k, pr = Send ch v k /\ pr' = k.
Proof.
  induct 1; simplify; try solve [ exfalso; eauto ].
  eapply output_typed' in H.
  first_order.
  eauto.
Qed.

Inductive typed_multistate party (channels : channel -> parties party) (t : type)
  : list party -> proc -> Prop :=
| TmsNil : typed_multistate channels t [] Done
| TmsCons : forall p ps pr1 pr2,
    hasty channels p false pr1 t
    -> typed_multistate channels t ps pr2
    -> typed_multistate channels t (p :: ps) (pr1 || pr2).

Hint Constructors typed_multistate.


Ltac side :=
  match goal with
  | [ |- ?E = {| Sender := _; Receiver := _ |} ] =>
    let E' := eval hnf in E in change E with E';
    repeat match goal with
           | [ |- context[if ?E then _ else _] ] => cases E; try (exfalso; equality)
           end;
    try (exfalso; equality);
    repeat match goal with
           | [ H : NoDup _ |- _ ] => invert H
           end; simplify; try (exfalso; equality); equality
  | [ |- _ <> _ ] => equality
  end.

Ltac hasty := simplify; repeat match goal with
                               | [ |- typed_multistate _ _ _ _ ] => econstructor; simplify
                               | [ |- hasty _ _ _ _ _ ] =>
                                 apply HtDone
                                 || (eapply HtSend; [ side | side | ])
                                 || (eapply HtRecv; [ constructor | side | side | simplify ])
                                 || (eapply HtSkip; [ constructor | side | side | side | simplify ])
                               | [ |- hasty _ _ _ _ (match ?E with _ => _ end) ] => cases E
                               | [ |- hasty _ _ _ (match ?E with _ => _ end) _ ] => cases E
                               end.

Lemma no_silent_steps : forall party (channels : _ -> parties party) p mns pr t,
    hasty channels p mns pr t
    -> forall pr', lstep pr Silent pr'
    -> False.
Proof.
  induct 1; invert 1; try solve [ exfalso; eauto ].
  Unshelve.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Hint Immediate no_silent_steps.

Lemma complementarity_forever_done : forall party (channels : _ -> parties party) pr pr',
  lstep pr Silent pr'
  -> forall all_parties, typed_multistate channels TDone all_parties pr
  -> False.
Proof.
  induct 1; invert 1; eauto.
  invert H5.
  invert H.
  invert H5.
  invert H.
Qed.

Lemma mayNotSend_really : forall party (channels : _ -> parties party) p pr t,
    hasty channels p true pr t
    -> forall m pr', lstep pr (Output m) pr'
                     -> False.
Proof.
  induct 1; eauto; invert 1.
  Unshelve.
  assumption.
Qed.

Hint Immediate mayNotSend_really.

Lemma may_not_output : forall (party : Set) pr pr' ch (A : Set) (v : A),
    lstep pr (Output {| Channel := ch; Value := v |}) pr'
    -> forall (channels : _ -> parties party) p t,
      hasty channels p true pr t
      -> False.
Proof.
  induct 1; invert 1; simplify; try solve [ exfalso; eauto ].
  Unshelve.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Hint Immediate may_not_output.

Lemma output_is_legit : forall (party : Set) pr pr' ch (A : Set) (v : A),
    lstep pr (Output {| Channel := ch; Value := v |}) pr'
    -> forall (channels : _ -> parties party) all_parties ch' (A' : Set) (k : A' -> _),
      typed_multistate channels (Communicate ch' k) all_parties pr
      -> In (Sender (channels ch')) all_parties.
Proof.
  induct 1; invert 1; simplify; try solve [ exfalso; eauto ].

  invert H4.
  rewrite H3 in *; simplify; eauto.
  invert H.
  exfalso; eauto.

  invert H4.
  rewrite H3 in *; simplify; eauto.
  eauto.
  eauto.

  Unshelve.
  assumption.
Qed.

Lemma output_is_first : forall (party : Set) pr pr' ch (A : Set) (v : A),
    lstep pr (Output {| Channel := ch; Value := v |}) pr'
    -> forall (channels : _ -> parties party) all_parties ch' (A' : Set) (k : A' -> _),
      typed_multistate channels (Communicate ch' k) all_parties pr
      -> ch' = ch.
Proof.
  induct 1; invert 1; simplify; try solve [ exfalso; eauto ].

  invert H4.
  invert H; auto.
  invert H.
  exfalso; eauto.

  eauto.

  Unshelve.
  assumption.
Qed.

Lemma input_is_legit' : forall (party : Set) pr ch (A : Set) (v : A)
                               (channels : _ -> parties party) p mns t,
    hasty channels p mns pr t
    -> forall pr', lstep pr (Input {| Channel := ch; Value := v |}) pr'
                   -> p = Receiver (channels ch).
Proof.
  induct 1; eauto; invert 1.
  rewrite H; auto.
Qed.

Lemma input_is_legit : forall (party : Set) pr pr' ch (A : Set) (v : A),
    lstep pr (Input {| Channel := ch; Value := v |}) pr'
    -> forall (channels : _ -> parties party) all_parties t,
      typed_multistate channels t all_parties pr
      -> In (Receiver (channels ch)) all_parties.
Proof.
  induct 1; invert 1; simplify; try solve [ exfalso; eauto ].

  invert H4.
  invert H.
  invert H.
  rewrite H0 in *; simplify; eauto.

  eapply input_is_legit' in H; eauto.

  invert H.

  eauto.

  Unshelve.
  assumption.
Qed.

Lemma absolutely_nobody : forall (party : Set) pr pr',
    lstep pr Silent pr'
    -> forall (channels : _ -> parties party) all_parties ch (A : Set) (k : A -> _),
      typed_multistate channels (Communicate ch k) all_parties pr
      -> (In (Sender (channels ch)) all_parties -> False)
      -> (In (Receiver (channels ch)) all_parties -> False)
      -> False.
Proof.
  induct 1; invert 1; simplify; try solve [ exfalso; eauto ].

  invert H4.
  rewrite H7 in *; simplify; eauto.
  rewrite H9 in *; simplify; eauto.
  eapply IHlstep; eauto.

  invert H5.
  rewrite H8 in *; simplify; eauto.
  rewrite H10 in *; simplify; eauto.
  eapply output_is_legit in H0; eauto.

  invert H5.
  rewrite H8 in *; simplify; eauto.
  rewrite H10 in *; simplify; eauto.
  eauto.

  Unshelve.
  assumption.
Qed.

Lemma comm_stuck : forall (party : Set) pr pr',
    lstep pr Silent pr'
    -> forall (channels : _ -> parties party) all_parties ch (A : Set) (k : A -> _),
      typed_multistate channels (Communicate ch k) all_parties pr
      -> (In (Sender (channels ch)) all_parties
          -> In (Receiver (channels ch)) all_parties
          -> False)
      -> False.
Proof.
  induct 1; invert 1; simplify; try solve [ exfalso; eauto ].

  invert H5.
  invert H.
  invert H.
  eapply output_is_legit in H0; eauto.
  rewrite H9 in *; simplify; eauto.
  rewrite H7 in *; simplify.
  eapply output_is_first in H0; eauto.
  subst.
  eapply input_is_legit' in H; eauto.
  subst.
  rewrite H7 in *.
  simplify.
  eauto.

  invert H5.
  invert H.
  rewrite H7 in *; simplify.
  eapply input_is_legit in H0; eauto.
  rewrite H7 in *; simplify.
  eauto.
  invert H.
  eauto.
  
  Unshelve.
  assumption.
  assumption.
Qed.

Lemma hasty_relax : forall party (channels : _ -> parties party) p mns pr t,
    hasty channels p mns pr t
    -> hasty channels p false pr t.
Proof.
  induct 1; eauto.
Qed.

Local Hint Immediate hasty_relax.

Lemma complementarity_preserve_unused : forall party (channels : _ -> parties party)
                                               pr ch (A : Set) (t : A -> _) all_parties,
    typed_multistate channels (Communicate ch t) all_parties pr
    -> ~In (Sender (channels ch)) all_parties
    -> ~In (Receiver (channels ch)) all_parties
    -> forall v, typed_multistate channels (t v) all_parties pr.
Proof.
  induct 1; simplify; eauto.
  invert H.
  rewrite H6 in *; simplify.
  equality.
  rewrite H8 in *; simplify.
  propositional.
  rewrite H6 in *; simplify.
  propositional.
  eauto.
Qed.

Lemma hasty_output : forall pr party (channels : _ -> parties party) p mns t,
    hasty channels p mns pr t
    -> forall ch (A : Set) (v : A) pr', lstep pr (Output {| Channel := ch; Value := v |}) pr'
      -> Sender (channels ch) = p.
Proof.
  induct 1; invert 1.
  rewrite H; auto.
  eauto.
  exfalso; eauto.
  exfalso; eauto.
  exfalso; eauto.

  Unshelve.
  assumption.
  assumption.
  assumption.
Qed.

Lemma complementarity_find_sender : forall party (channels : _ -> parties party) pr ch (A : Set) (v : A) pr',
  lstep pr (Output {| Channel := ch; Value := v |}) pr'
  -> forall (t : A -> _) all_parties,
      typed_multistate channels (Communicate ch t) all_parties pr
      -> NoDup all_parties
      -> In (Sender (channels ch)) all_parties
      -> ~In (Receiver (channels ch)) all_parties
      -> typed_multistate channels (t v) all_parties pr'.
Proof.
  induct 1; invert 1; simplify; try solve [ exfalso; eauto ].

  invert H0.
  generalize dependent H.
  invert H4.
  invert 1.
  econstructor.
  eauto.
  eapply complementarity_preserve_unused; eauto.
  rewrite H6; assumption.
  invert 1.
  rewrite H6 in *; simplify.
  eapply hasty_output in H; eauto.
  rewrite H6 in *; simplify.
  equality.

  invert H0.
  invert H4.
  rewrite H9 in *; simplify.  
  eapply output_is_legit in H5; try eassumption.
  rewrite H9 in *; simplify.
  propositional.
  rewrite H11 in *; simplify.
  propositional.
  rewrite H9 in *; simplify.

  eapply IHlstep in H5; try (eassumption || reflexivity).
  2: rewrite H9; simplify; equality.
  2: rewrite H9; simplify; equality.
  eauto.

  Unshelve.
  assumption.
Qed.

Lemma complementarity_find_receiver : forall party (channels : _ -> parties party) pr ch (A : Set) (v : A) pr',
  lstep pr (Input {| Channel := ch; Value := v |}) pr'
  -> forall (t : A -> _) all_parties,
      typed_multistate channels (Communicate ch t) all_parties pr
      -> NoDup all_parties
      -> ~In (Sender (channels ch)) all_parties
      -> In (Receiver (channels ch)) all_parties
      -> typed_multistate channels (t v) all_parties pr'.
Proof.
  induct 1; invert 1; simplify; try solve [ exfalso; eauto ].

  invert H0.
  generalize dependent H.
  invert H4.
  invert 1.
  invert 1.
  econstructor.
  eauto.
  eapply complementarity_preserve_unused; eauto.
  rewrite H10; assumption.
  rewrite H6 in *; simplify.
  eapply input_is_legit' in H; eauto.
  rewrite H6 in *; simplify; equality.

  invert H0.
  invert H4.
  rewrite H9 in *; simplify.
  eapply input_is_legit in H; try eassumption.
  rewrite H9 in *; simplify.
  propositional.
  rewrite H11 in *; simplify.
  propositional.
  eapply input_is_legit in H; try eassumption.
  rewrite H11 in *; simplify.
  propositional.
  eapply IHlstep in H5; try (eassumption || reflexivity).
  2: rewrite H9 in *; simplify; equality.
  2: rewrite H9 in *; simplify; equality.
  eauto.

  Unshelve.
  assumption.
Qed.

Lemma output_is_legit' : forall party (channels : _ -> parties party) p mns pr t,
    hasty channels p mns pr t
    -> forall ch (A : Set) (v : A) pr', lstep pr (Output {| Channel := ch; Value := v |}) pr'
    -> p = Sender (channels ch).
Proof.
  induct 1; invert 1; simplify; try solve [ exfalso; eauto ].
  rewrite H; auto.

  Unshelve.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma complementarity_forever' : forall party (channels : _ -> parties party) pr pr',
  lstep pr Silent pr'
  -> forall ch (A : Set) (t : A -> _) all_parties,
      typed_multistate channels (Communicate ch t) all_parties pr
      -> NoDup all_parties
      -> In (Sender (channels ch)) all_parties
      -> In (Receiver (channels ch)) all_parties
      -> exists v, typed_multistate channels (t v) all_parties pr'.
Proof.
  induct 1; invert 1; simplify; try solve [ exfalso; eauto ].

  invert H0.
  invert H4.
  rewrite H9 in *; simplify.
  propositional; try equality.

  exfalso; eapply comm_stuck; try eassumption.
  rewrite H9; simplify; eauto.

  exfalso; eapply comm_stuck; try eassumption.  
  rewrite H11; simplify; eauto.

  rewrite H9 in *; simplify.
  apply IHlstep in H5; try assumption.
  2: rewrite H9; simplify; equality.
  2: rewrite H9; simplify; equality.
  first_order; eauto.

  invert H1.
  generalize dependent H.
  invert H5.
  invert 1.
  invert 1.
  eexists.
  econstructor.
  eauto.
  eapply complementarity_find_sender; try eassumption.
  rewrite H11 in *; simplify; equality.
  rewrite H11 in *; simplify; equality.
  rewrite H7 in *; simplify.
  eapply input_is_legit' in H; eauto.
  eapply output_is_first in H6; try eassumption.
  subst.
  rewrite H7 in *; simplify; equality.

  invert H1.
  generalize dependent H.
  invert H5.
  invert 1.
  eexists.
  econstructor.
  eauto.
  eapply complementarity_find_receiver; try eassumption.
  rewrite H7 in *; simplify; equality.
  rewrite H7 in *; simplify; equality.
  invert 1.
  rewrite H7 in *; simplify.
  exfalso; eauto.

  Unshelve.
  assumption.
  assumption.
Qed.

Lemma complementarity_forever : forall party (channels : _ -> parties party) all_parties pr t,
    NoDup all_parties
    -> (forall p, In p all_parties)
    -> typed_multistate channels t all_parties pr
    -> invariantFor (trsys_of pr)
                    (fun pr' => exists t',
                         typed_multistate channels t' all_parties pr').
Proof.
  simplify.
  apply invariant_induction; simplify.

  propositional; subst.
  eauto.

  clear pr t H1.
  first_order.
  cases x.
  eapply complementarity_forever' in H1; try eassumption.
  first_order.
  eauto.
  eauto.

  exfalso; eauto using complementarity_forever_done.
Qed.

Inductive inert : proc -> Prop :=
| InertDone : inert Done
| InertPar : forall pr1 pr2,
    inert pr1
    -> inert pr2
    -> inert (pr1 || pr2).

Hint Constructors inert.

Lemma typed_multistate_inert : forall party (channels : _ -> parties party) all_parties pr,
    typed_multistate channels TDone all_parties pr
    -> inert pr.
Proof.
  induct 1; eauto.
  invert H; eauto.
Qed.

Hint Immediate typed_multistate_inert.

Lemma deadlock_find_receiver : forall party (channels : _ -> parties party) all_parties
                                      ch (A : Set) (k : A -> _) pr,
    typed_multistate channels (Communicate ch k) all_parties pr
    -> In (Receiver (channels ch)) all_parties
    -> forall v : A, exists pr', lstep pr (Input {| Channel := ch; Value := v |}) pr'.
Proof.
  induct 1; simplify; propositional; subst.

  invert H.
  rewrite H4 in *; simplify.
  equality.
  eauto.
  rewrite H4 in *; simplify.
  equality.

  invert H.
  rewrite H6 in *; simplify.
  specialize (H1 v).
  first_order.
  eauto.
  rewrite H8 in *; simplify.
  eauto.

  rewrite H6 in *; simplify.
  specialize (H1 v).
  first_order.
  eauto.
Qed.

Lemma deadlock_find_sender : forall party (channels : _ -> parties party) all_parties
                                    ch (A : Set) (k : A -> _) pr,
    typed_multistate channels (Communicate ch k) all_parties pr
    -> In (Sender (channels ch)) all_parties
    -> exists (v : A) pr', lstep pr (Output {| Channel := ch; Value := v |}) pr'.
Proof.
  induct 1; simplify; propositional; subst.

  invert H.
  rewrite H4 in *; simplify.
  eauto.
  rewrite H6 in *; simplify.
  equality.
  rewrite H4 in *; simplify.
  equality.

  first_order.
  invert H.
  rewrite H6 in *; simplify.
  eauto.
  rewrite H8 in *; simplify.
  eauto.

  eauto.
Qed.

Lemma no_deadlock' : forall party (channels : _ -> parties party) all_parties
                            ch (A : Set) (k : A -> _) pr,
    NoDup all_parties
    -> typed_multistate channels (Communicate ch k) all_parties pr
    -> In (Sender (channels ch)) all_parties
    -> In (Receiver (channels ch)) all_parties
    -> exists pr', lstep pr Silent pr'.
Proof.
  induct 2; simplify; propositional; subst.

  invert H0.
  rewrite H6 in *; simplify.
  equality.
  rewrite H8 in *; simplify.
  equality.
  rewrite H6 in *; simplify.
  equality.

  invert H0.
  rewrite H6 in *; simplify.
  eapply deadlock_find_receiver in H1.
  first_order; eauto.
  rewrite H6; assumption.
  rewrite H8 in *; simplify.
  equality.
  rewrite H6 in *; simplify.
  equality.

  invert H0.
  rewrite H6 in *; simplify.
  equality.
  rewrite H8 in *; simplify.
  eapply deadlock_find_sender in H1.
  first_order; eauto.
  rewrite H8; assumption.
  rewrite H6 in *; simplify.
  equality.

  invert H.
  apply IHtyped_multistate in H7; auto.
  first_order; eauto.
Qed.

Theorem no_deadlock : forall party (channels : _ -> parties party) all_parties pr t,
    NoDup all_parties
    -> (forall p, In p all_parties)
    -> typed_multistate channels t all_parties pr
    -> invariantFor (trsys_of pr)
                    (fun pr => inert pr
                               \/ exists pr', lstep pr Silent pr').
Proof.
  simplify.
  eapply invariant_weaken.
  eapply complementarity_forever; eassumption.

  clear pr t H1.
  simplify; first_order.
  cases x.
  right; eapply no_deadlock'; try eassumption; eauto.
  eauto.
Qed.

Inductive store_party := Customer | Merchant.

Section online_store.
  Variables request_product in_stock_or_not send_payment_info payment_success add_review : channel.

  Definition customer (product payment_info : string) :=
    !!request_product(product);
    ??in_stock_or_not(worked : bool);
    if worked then
      !!send_payment_info(payment_info);
      ??payment_success(worked_again : bool);
      if worked_again then
        !!add_review((product, "awesome"));
        Done
      else
        Done
    else
      Done.

  Definition merchant (in_stock payment_checker : string -> bool) :=
    ??request_product(product : string);
    if in_stock product then
      !!in_stock_or_not(true);
      ??send_payment_info(payment_info : string);
      if payment_checker payment_info then
        !!payment_success(true);
        ??add_review(_ : (string * string)%type);
        Done
      else
        !!payment_success(false);
        Done
    else
      !!in_stock_or_not(false);
      Done.

  Definition online_store_type :=
    (!!!request_product(_ : string);
     !!!in_stock_or_not(worked : bool);
     if worked then
       !!!send_payment_info(_ : string);
       !!!payment_success(worked_again : bool);
       if worked_again then
         !!!add_review(_ : (string * string)%type);
         TDone
       else
         TDone
     else
       TDone)%st.

  Definition online_store_channels (ch : channel) :=
    if ch ==n request_product then
      {| Sender := Customer;
         Receiver := Merchant |}
    else if ch ==n send_payment_info then
      {| Sender := Customer;
         Receiver := Merchant |}
    else if ch ==n add_review then
      {| Sender := Customer;
         Receiver := Merchant |}
    else
      {| Sender := Merchant;
         Receiver := Customer |}.

  Example online_store_no_deadlock : forall product payment_info in_stock payment_checker,
      NoDup [request_product; in_stock_or_not; send_payment_info; payment_success; add_review]
      -> invariantFor (trsys_of (customer product payment_info
                                 || (merchant in_stock payment_checker
                                     || Done)))
                      (fun pr => inert pr
                                 \/ exists pr', lstep pr Silent pr').
  Proof.
    simplify.
    eapply no_deadlock with (t := online_store_type)
                            (all_parties := [Customer; Merchant])
                            (channels := online_store_channels);
    simplify.

    repeat constructor; simplify; equality.

    cases p; auto.

    hasty; constructor.
  Qed.
End online_store.

Inductive store_party' := Customer' | Merchant' | Warehouse.

Section online_store_with_warehouse.
  Variables request_product in_stock_or_not send_payment_info payment_success add_review
            merchant_to_warehouse warehouse_to_merchant : channel.

  Definition customer' (product payment_info : string) :=
    !!request_product(product);
    ??in_stock_or_not(worked : bool);
    if worked then
      !!send_payment_info(payment_info);
      ??payment_success(worked_again : bool);
      if worked_again then
        !!add_review((product, "awesome"));
        Done
      else
        Done
    else
      Done.

  Definition merchant' (payment_checker : string -> bool) :=
    ??request_product(product : string);
    !!merchant_to_warehouse(product);
    ??warehouse_to_merchant(in_stock : bool);
    if in_stock then
      !!in_stock_or_not(true);
      ??send_payment_info(payment_info : string);
      if payment_checker payment_info then
        !!payment_success(true);
        ??add_review(_ : (string * string)%type);
        Done
      else
        !!payment_success(false);
        Done
    else
      !!in_stock_or_not(false);
      Done.

  Definition warehouse (in_stock : string -> bool) :=
    ??merchant_to_warehouse(product : string);
    if in_stock product then
      !!warehouse_to_merchant(true);
      Done
    else
      !!warehouse_to_merchant(false);
      Done.

  Definition online_store_type' :=
    (!!!request_product(_ : string);
     !!!merchant_to_warehouse(_ : string);
     !!!warehouse_to_merchant(_ : bool);
     !!!in_stock_or_not(worked : bool);
     if worked then
       !!!send_payment_info(_ : string);
       !!!payment_success(worked_again : bool);
       if worked_again then
         !!!add_review(_ : (string * string)%type);
         TDone
       else
         TDone
     else
       TDone)%st.

  Definition online_store_channels' (ch : channel) :=
    if ch ==n request_product then
      {| Sender := Customer';
         Receiver := Merchant' |}
    else if ch ==n send_payment_info then
      {| Sender := Customer';
         Receiver := Merchant' |}
    else if ch ==n add_review then
      {| Sender := Customer';
         Receiver := Merchant' |}
    else if ch ==n merchant_to_warehouse then
      {| Sender := Merchant';
         Receiver := Warehouse |}
    else if ch ==n warehouse_to_merchant then
      {| Sender := Warehouse;
         Receiver := Merchant' |}
    else
      {| Sender := Merchant';
         Receiver := Customer' |}.

  Example online_store_no_deadlock' : forall product payment_info in_stock good_infos,
      NoDup [request_product; in_stock_or_not; send_payment_info; payment_success; add_review;
             merchant_to_warehouse; warehouse_to_merchant]
      -> invariantFor (trsys_of (customer' product payment_info
                                 || (merchant' in_stock
                                     || (warehouse good_infos || Done))))
                      (fun pr => inert pr
                                 \/ exists pr', lstep pr Silent pr').
  Proof.
    simplify.
    eapply no_deadlock with (t := online_store_type')
                            (all_parties := [Customer'; Merchant'; Warehouse])
                            (channels := online_store_channels');
    simplify.

    repeat constructor; simplify; equality.

    cases p; auto.

    hasty; constructor.
  Qed.
End online_store_with_warehouse.

End Multiparty.
