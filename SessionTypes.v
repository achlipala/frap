(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 20: Session Types
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap FunctionalExtensionality MessagesAndRefinement.

Set Implicit Arguments.
Set Asymmetric Patterns.


(* One natural view of process algebra is as a way of orchestrating multiple
 * agents that communicate with each other through prearranged protocols.
 * Session types are a way of doing static analysis, in the style of type
 * checking as we saw in earlier chapters, to guarantee that agents play well
 * together.  Specifically, in this chapter, we'll confine our attention to
 * avoiding stuckness: a set of agents should either reach a state where
 * everyone is done or should continue stepping forever.  A counterexample would
 * be a configuration where each of two agents is blocked waiting for input from
 * the other -- a classic deadlock. *)


(** * Basic Two-Party Session Types *)

(* We'll consider some gradations of fanciness in our session type systems.
 * Even the final version will have some notable expressiveness weaknesses, but
 * we'll still be able to handle a variety of nontrivial protocols.  Each
 * variant will be confined to its own module, allowing us to reuse names. *)

Module BasicTwoParty.

(** ** Defining the type system *)

Inductive type :=
| TSend (ch : channel) (A : Type) (t : type)
(* This type applies to a process that begins by sending a value of type [A]
 * over channel [ch], then continuing according to type [t]. *)

| TRecv (ch : channel) (A : Type) (t :  type)
(* This type is the dual of the last one: the process begins by receiving a
 * value of type [A] from channel [ch]. *)

| TDone.
(* This type describes processes that are done.  Notice that we make our lives
 * easier by not supporting any of the other constructs (parallel composition,
 * duplication, ...) from our process algebra! *)

(* The typing rules mostly just formalize the comments from above. *)
Inductive hasty : proc -> type -> Prop :=
| HtSend : forall ch (A : Type) (v : A) k t,
    hasty k t
    -> hasty (Send ch v k) (TSend ch A t)
| HtRecv : forall ch (A : Type) (k : A -> _) t,
    (forall v, hasty (k v) t)
    -> hasty (Recv ch k) (TRecv ch A t)
| HtDone :
    hasty Done TDone.
(* Notice, though, that the premise of [HtRecv] does quantification over all
 * possible values that might come down the channel [ch].  The follow-up type [t]
 * must be independent of those values, though. *)

(* Some notations will let us write nicer-looking types. *)
Delimit Scope st_scope with st.
Bind Scope st_scope with type.
Notation "!!! ch ( A ) ; k" := (TSend ch A k%st) (right associativity, at level 45, ch at level 0) : st_scope.
Notation "??? ch ( A ) ; k" := (TRecv ch A k%st) (right associativity, at level 45, ch at level 0) : st_scope.

(* This tactic happens to be good for automating typing derivations. *)
Ltac hasty := simplify; repeat ((constructor; simplify)
                                || match goal with
                                   | [ |- hasty _ (match ?E with _ => _ end) ] => cases E
                                   | [ |- hasty (match ?E with _ => _ end) _ ] => cases E
                                   end).

(** * Examples of typed processes *)

(* Recall our first example from last chapter. *)
Definition addN (k : nat) (input output : channel) : proc :=
  ??input(n : nat);
  !!output(n + k);
  Done.

(* Let's prove it against a type, which looks a lot like the program itself. *)
Definition addN_type input output :=
  (???input(nat); !!!output(nat); TDone)%st.

Theorem addN_typed : forall k input output,
    hasty (addN k input output) (addN_type input output).
Proof.
  hasty.
Qed.


(** * Complementing types *)

(* We will focus on pairs of interacting processes, where one process follows a
 * session type, and the other process follows the *complement* of that type,
 * guaranteeing that they agree on the protocol. *)

(* Complementation just flips all sends and receives. *)
Fixpoint complement (t : type) : type :=
  match t with
  | TSend ch A t1 => TRecv ch A (complement t1)
  | TRecv ch A t1 => TSend ch A (complement t1)
  | TDone => TDone
  end.

(* Here's a simple client for our adder example. *)
Definition add2_client (input output : channel) : proc :=
  !!input(42);
  ??output(_ : nat);
  Done.

(* It checks out against the complement of the type from before. *)
Theorem add2_client_typed : forall input output,
    hasty (add2_client input output) (complement (addN_type input output)).
Proof.
  hasty.
Qed.


(** * Main theorem: deadlock freedom for complementary processes *)

Definition trsys_of pr := {|
  Initial := {pr};
  Step := lstepSilent
|}.
(* Note: here we force silent steps, so that all channel communication is
 * internal. *)

Hint Constructors hasty : core.

(* The next two lemmas state some inversions that connect stepping and
 * typing. *)

Lemma input_typed : forall pr ch A v pr',
    lstep pr (Action (Input {| Channel := ch; TypeOf := A; Value := v |})) pr'
    -> forall t, hasty pr t
                 -> exists k, pr = Recv ch k /\ pr' = k v.
Proof.
  invert 1; invert 1; eauto.
Qed.

Lemma output_typed : forall pr ch A v pr',
    lstep pr (Action (Output {| Channel := ch; TypeOf := A; Value := v |})) pr'
    -> forall t, hasty pr t
                 -> exists k, pr = Send ch v k /\ pr' = k.
Proof.
  invert 1; invert 1; eauto.
Qed.

(* A key strengthened invariant: when two processes begin life as complementary,
 * they remain complementary forever after, though the shared type may
 * change. *)
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

(* The main theorem: it's an invariant that the system is done or can take a
 * step. *)
Theorem no_deadlock : forall pr1 pr2 t,
    hasty pr1 t
    -> hasty pr2 (complement t)
    -> invariantFor (trsys_of (pr1 || pr2))
                    (fun pr => pr = (Done || Done)
                               \/ exists pr', lstep pr Silent pr').
Proof.
  simplify.
  eapply invariant_weaken.
  eapply complementarity_forever; eauto.

  clear pr1 pr2 t H H0.
  simplify; first_order; subst.
  invert H0; invert H1; simplify; eauto.
Qed.

(* Applying the theorem to our earlier example is easy. *)
Example adding_no_deadlock : forall k input output,
    input <> output
    -> invariantFor (trsys_of (addN k input output
                               || add2_client input output))
               (fun pr => pr = (Done || Done)
                          \/ exists pr', lstep pr Silent pr').
Proof.
  simplify.
  eapply no_deadlock with (t := addN_type input output);
    hasty.
Qed.

End BasicTwoParty.


(** * Two-Party Session Types *)

(* That last type system has a serious weakness: it doesn't allow communication
 * patterns to vary, based on what was received on channels earlier in
 * execution.  Let's switch to a simple kind of *dependent* session types, where
 * send and receive types bind message values for use in decision-making. *)

Module TwoParty.

(** ** Defining the type system *)

Inductive type :=
| TSend (ch : channel) (A : Type) (t : A -> type)
| TRecv (ch : channel) (A : Type) (t : A -> type)
| TDone.
(* Note the big change: each follow-up type [t] is parameterized on the value
 * sent or received.  As with our mixed-embedding programs, within these
 * functions we may employ the full expressiveness of Gallina. *)

Inductive hasty : proc -> type -> Prop :=
| HtSend : forall ch (A : Type) (v : A) k t,
    hasty k (t v)
    -> hasty (Send ch v k) (TSend ch t)
| HtRecv : forall ch (A : Type) (k : A -> _) t,
    (forall v, hasty (k v) (t v))
    -> hasty (Recv ch k) (TRecv ch t)
| HtDone :
    hasty Done TDone.

Delimit Scope st_scope with st.
Bind Scope st_scope with type.
Notation "!!! ch ( x : A ) ; k" := (TSend ch (fun x : A => k)%st) (right associativity, at level 45, ch at level 0, x at level 0) : st_scope.
Notation "??? ch ( x : A ) ; k" := (TRecv ch (fun x : A => k)%st) (right associativity, at level 45, ch at level 0, x at level 0) : st_scope.

Ltac hasty := simplify; repeat ((constructor; simplify)
                                || match goal with
                                   | [ |- hasty _ (match ?E with _ => _ end) ] => cases E
                                   | [ |- hasty (match ?E with _ => _ end) _ ] => cases E
                                   end).

(** * Complementing types *)

Fixpoint complement (t : type) : type :=
  match t with
  | TSend ch _ t1 => TRecv ch (fun v => complement (t1 v))
  | TRecv ch _ t1 => TSend ch (fun v => complement (t1 v))
  | TDone => TDone
  end.

(** ** Example *)

(* Let's demonstrate the power of the strengthened type system.  We'll model an
 * online store communicating with a customer. *)
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
  (* Yes, that type again looks a lot like the program!  However, we abstract
   * away the details of all non-[bool] messages. *)

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


(** * Main theorem: deadlock freedom for complementary processes *)

(* The proof is essentially identical to before, which is kind of neat, given
 * the fundamental new capability that we added. *)

Definition trsys_of pr := {|
  Initial := {pr};
  Step := lstepSilent
|}.

Hint Constructors hasty : core.

Lemma input_typed : forall pr ch A v pr',
    lstep pr (Action (Input {| Channel := ch; TypeOf := A; Value := v |})) pr'
    -> forall t, hasty pr t
                 -> exists k, pr = Recv ch k /\ pr' = k v.
Proof.
  invert 1; invert 1; eauto.
Qed.

Lemma output_typed : forall pr ch A v pr',
    lstep pr (Action (Output {| Channel := ch; TypeOf := A; Value := v |})) pr'
    -> forall t, hasty pr t
                 -> exists k, pr = Send ch v k /\ pr' = k.
Proof.
  invert 1; invert 1; eauto.
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
                               \/ exists pr', lstep pr Silent pr').
Proof.
  simplify.
  eapply invariant_weaken.
  eapply complementarity_forever; eauto.

  clear pr1 pr2 t H H0.
  simplify; first_order; subst.
  invert H0; invert H1; simplify; eauto.
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
                          \/ exists pr', lstep pr Silent pr').
Proof.
  simplify.
  eapply no_deadlock with (t := customer_type request_product in_stock_or_not
                                              send_payment_info payment_success add_review);
    hasty.
Qed.

End TwoParty.


(** * Multiparty Session Types *)

(* Let's generalize to any number of agents participating in a protocol.  We
 * won't support all reasonable protocols, and it's an edifying exercise for the
 * reader to think up examples that this type system rejects. *)

Module Multiparty.

(** ** Defining the type system *)

Inductive type :=
| Communicate (ch : channel) (A : Type) (t : A -> type)
| TDone.
(* Things are quite different now.  We define one protocol with a series of
 * communications, not specifying read vs. write polarity.  Every agent will be
 * checked against this type, referring to a mapping that tells us which agent
 * controls the receive end and which the send end of each channel.  Exactly one
 * agent will have each role. *)

Delimit Scope st_scope with st.
Bind Scope st_scope with type.
Notation "!!! ch ( x : A ) ; k" := (Communicate ch (fun x : A => k)%st) (right associativity, at level 45, ch at level 0, x at level 0) : st_scope.

Section parties.
  Variable party : Type.
  (* We will formalize typing with respect to some (usually finite) set of
   * parties/agents. *)

  Record parties := {
    Sender : party;
    Receiver : party
  }.
  Variable channels : channel -> parties.
  (* As promised, every channel is assigned a unique sender and receiver. *)

  Inductive hasty (p : party) : bool -> proc -> type -> Prop :=

  (* The first two rules look up the next channel and confirm that the current
   * process is in the right role to perform a send or receive. *)
  | HtSend : forall ch rr (A : Type) (v : A) k t,
    channels ch = {| Sender := p; Receiver := rr |}
    -> rr <> p
    -> hasty p false k (t v)
    -> hasty p false (Send ch v k) (Communicate ch t)
  | HtRecv : forall mayNotSend ch sr (A : Type) (k : A -> _) t (witness : A),
      channels ch = {| Sender := sr; Receiver := p |}
      -> sr <> p
      -> (forall v, hasty p false (k v) (t v))
      -> hasty p mayNotSend (Recv ch k) (Communicate ch t)

  (* Not all parties participate in all communications.  Uninvolved parties may
   * (or, rather, must!) skip protocol steps. *)
  | HtSkip : forall mayNotSend ch sr rr (A : Type) pr (t : A -> _) (witness : A),
      channels ch = {| Sender := sr; Receiver := rr |}
      -> sr <> p
      -> rr <> p
      -> (forall v, hasty p true pr (t v))
      -> hasty p mayNotSend pr (Communicate ch t)

  | HtDone : forall mayNotSend,
      hasty p mayNotSend Done TDone.

  (* What was that peculiar [bool] parameter?  If [true], it prohibits the
   * process from running a [Send] as its next action.  The idea is that, when a
   * process sits out one step of a protocol, its next action (if any) had
   * better be a receive, so that it gets some signal to wake up and resume
   * participating.  Otherwise, the deadlock-freedom analysis is more
   * complicated. *)
End parties.


(** * Main theorem: deadlock freedom for complementary processes *)

Definition trsys_of pr := {|
  Initial := {pr};
  Step := lstepSilent
|}.

Hint Constructors hasty : core.

(* We prove that the type system rules out fancier constructs. *)

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

Hint Immediate hasty_not_Block hasty_not_Dup hasty_not_Par : core.

(* Next, we characterize how channels must be mapped, given typing of a
 * process. *)

Lemma input_typed' : forall party (channels : _ -> parties party) p mns ch (A : Type) (k : A -> _) t,
    hasty channels p mns (Recv ch k) t
    -> exists sr (witness : A), channels ch = {| Sender := sr; Receiver := p |}
                                /\ sr <> p.
Proof.
  induct 1; eauto.
  Unshelve.
  assumption.
Qed.

Lemma input_typed : forall party (channels: _ -> parties party) pr ch A v pr',
    lstep pr (Action (Input {| Channel := ch; TypeOf := A; Value := v |})) pr'
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

Lemma output_typed' : forall party (channels : _ -> parties party) p mns ch (A : Type) (v : A) k t,
    hasty channels p mns (Send ch v k) t
    -> exists rr, channels ch = {| Sender := p; Receiver := rr |}
                  /\ rr <> p.
Proof.
  induct 1; eauto.
  Unshelve.
  assumption.
Qed.

Lemma output_typed : forall party (channels: _ -> parties party) pr ch A v pr',
    lstep pr (Action (Output {| Channel := ch; TypeOf := A; Value := v |})) pr'
    -> forall p mns t, hasty channels p mns pr t
                       -> exists k, pr = Send ch v k /\ pr' = k.
Proof.
  induct 1; simplify; try solve [ exfalso; eauto ].
  eapply output_typed' in H.
  first_order.
  eauto.
Qed.

(* Here is a crucial additional typing judgment, applying to lists of parties.
 * The parties' code is lined up with lopsided trees of parallel composition. *)
Inductive typed_multistate party (channels : channel -> parties party) (t : type)
  : list party -> proc -> Prop :=
| TmsNil : typed_multistate channels t [] Done
| TmsCons : forall p ps pr1 pr2,
    hasty channels p false pr1 t
    -> typed_multistate channels t ps pr2
    -> typed_multistate channels t (p :: ps) (pr1 || pr2).

Hint Constructors typed_multistate : core.

(* This fancier typing judgment gets a fancier tactic for type-checking. *)

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

(* Now follow quite a few fiddly lemmas.  Commentary resumes at a crucial
 * lemma. *)

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

Hint Immediate no_silent_steps : core.

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
    -> forall m pr', lstep pr (Action (Output m)) pr'
                     -> False.
Proof.
  induct 1; eauto; invert 1.
  Unshelve.
  assumption.
Qed.

Hint Immediate mayNotSend_really : core.

Lemma may_not_output : forall (party : Type) pr pr' ch (A : Type) (v : A),
    lstep pr (Action (Output {| Channel := ch; Value := v |})) pr'
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

Hint Immediate may_not_output : core.

Lemma output_is_legit : forall (party : Type) pr pr' ch (A : Type) (v : A),
    lstep pr (Action (Output {| Channel := ch; Value := v |})) pr'
    -> forall (channels : _ -> parties party) all_parties ch' (A' : Type) (k : A' -> _),
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


Lemma output_is_first : forall (party : Type) pr pr' ch (A : Type) (v : A),
    lstep pr (Action (Output {| Channel := ch; Value := v |})) pr'
    -> forall (channels : _ -> parties party) all_parties ch' (A' : Type) (k : A' -> _),
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

Lemma input_is_legit' : forall (party : Type) pr ch (A : Type) (v : A)
                               (channels : _ -> parties party) p mns t,
    hasty channels p mns pr t
    -> forall pr', lstep pr (Action (Input {| Channel := ch; Value := v |})) pr'
                   -> p = Receiver (channels ch).
Proof.
  induct 1; eauto; invert 1.
  rewrite H; auto.
Qed.

Lemma input_is_legit : forall (party : Type) pr pr' ch (A : Type) (v : A),
    lstep pr (Action (Input {| Channel := ch; Value := v |})) pr'
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

Lemma comm_stuck : forall (party : Type) pr pr',
    lstep pr Silent pr'
    -> forall (channels : _ -> parties party) all_parties ch (A : Type) (k : A -> _),
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

Local Hint Immediate hasty_relax : core.

Lemma complementarity_preserve_unused : forall party (channels : _ -> parties party)
                                               pr ch (A : Type) (t : A -> _) all_parties,
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
    -> forall ch (A : Type) (v : A) pr', lstep pr (Action (Output {| Channel := ch; Value := v |})) pr'
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

Lemma complementarity_find_sender : forall party (channels : _ -> parties party) pr ch (A : Type) (v : A) pr',
  lstep pr (Action (Output {| Channel := ch; Value := v |})) pr'
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

Lemma complementarity_find_receiver : forall party (channels : _ -> parties party) pr ch (A : Type) (v : A) pr',
  lstep pr (Action (Input {| Channel := ch; Value := v |})) pr'
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
    -> forall ch (A : Type) (v : A) pr', lstep pr (Action (Output {| Channel := ch; Value := v |})) pr'
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
  -> forall ch (A : Type) (t : A -> _) all_parties,
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

(* Note how the strengthened invariant here is a natural analogue of the one
 * for our previous type system.  Instead of calling out two composed actors, we
 * use predicate [typed_multistate] to constrain process [pr] to include all
 * parties from [all_parties]. *)
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

(* To state deadlock-freedom, it will help to have a general characterization of
 * when a set of agents are completely finished running. *)
Inductive inert : proc -> Prop :=
| InertDone : inert Done
| InertPar : forall pr1 pr2,
    inert pr1
    -> inert pr2
    -> inert (pr1 || pr2).

Hint Constructors inert : core.

(* Now a few more fiddly lemmas.  See you again at the [Theorem]. *)

Lemma typed_multistate_inert : forall party (channels : _ -> parties party) all_parties pr,
    typed_multistate channels TDone all_parties pr
    -> inert pr.
Proof.
  induct 1; eauto.
  invert H; eauto.
Qed.

Hint Immediate typed_multistate_inert : core.

Lemma deadlock_find_receiver : forall party (channels : _ -> parties party) all_parties
                                      ch (A : Type) (k : A -> _) pr,
    typed_multistate channels (Communicate ch k) all_parties pr
    -> In (Receiver (channels ch)) all_parties
    -> forall v : A, exists pr', lstep pr (Action (Input {| Channel := ch; Value := v |})) pr'.
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
                                    ch (A : Type) (k : A -> _) pr,
    typed_multistate channels (Communicate ch k) all_parties pr
    -> In (Sender (channels ch)) all_parties
    -> exists (v : A) pr', lstep pr (Action (Output {| Channel := ch; Value := v |})) pr'.
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
                            ch (A : Type) (k : A -> _) pr,
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

(* The statement is pleasingly similar to for our prior type system.  The main
 * new wrinkle is the list [all_parties] of all possible parties, as the first
 * two hypotheses enforce. *)
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

(* Let's redo our online-store example as a degenerate case of multiparty
 * protocols. *)

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

(* Next, let's add a new party, to exercise the type system more fully. *)

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

  Example online_store_no_deadlock' : forall product payment_info payment_checker in_stock,
      NoDup [request_product; in_stock_or_not; send_payment_info; payment_success; add_review;
             merchant_to_warehouse; warehouse_to_merchant]
      -> invariantFor (trsys_of (customer' product payment_info
                                 || (merchant' payment_checker
                                     || (warehouse in_stock || Done))))
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


(** * A bonus: running orthogonal protocols in parallel *)

Inductive mayTouch : proc -> channel -> Prop :=
| MtSend1 : forall ch (A : Type) (v : A) k,
    mayTouch (Send ch v k) ch
| MtSend2 : forall ch (A : Type) (v : A) k ch',
    mayTouch k ch'
    -> mayTouch (Send ch v k) ch'
| MtRecv1 : forall ch (A : Type) (k : A -> _),
    mayTouch (Recv ch k) ch
| MtRecv2 : forall ch (A : Type) (v : A) k ch',
    mayTouch (k v) ch'
    -> mayTouch (Recv ch k) ch'
| MtNewChannel : forall ch chs ch' k,
    mayTouch (k ch') ch
    -> mayTouch (NewChannel chs k) ch
| MtBlockChannel : forall ch ch' k,
    mayTouch k ch
    -> mayTouch (BlockChannel ch' k) ch
| MtPar1 : forall ch pr1 pr2,
    mayTouch pr1 ch
    -> mayTouch (Par pr1 pr2) ch
| MtPar2 : forall ch pr1 pr2,
    mayTouch pr2 ch
    -> mayTouch (Par pr1 pr2) ch
| MtDup : forall ch pr1,
    mayTouch pr1 ch
    -> mayTouch (Dup pr1) ch.

Hint Constructors mayTouch : core.

Import BasicTwoParty Multiparty.

Lemma lstep_mayTouch : forall pr l pr',
    lstep pr l pr'
    -> forall ch, mayTouch pr' ch -> mayTouch pr ch.
Proof.
  induct 1; invert 1; eauto;
    eapply MtRecv2;
    match goal with
    | [ H : _ = _ |- _ ] => rewrite <- H; eauto
    end.
Qed.

Hint Immediate lstep_mayTouch : core.

Lemma Input_mayTouch : forall pr ch (A : Type) (v : A) pr',
    lstep pr (Action (Input {| Channel := ch; Value := v |})) pr'
    -> mayTouch pr ch.
Proof.
  induct 1; eauto.
Qed.

Lemma Output_mayTouch : forall pr ch (A : Type) (v : A) pr',
    lstep pr (Action (Output {| Channel := ch; Value := v |})) pr'
    -> mayTouch pr ch.
Proof.
  induct 1; eauto.
Qed.

Hint Immediate Input_mayTouch Output_mayTouch : core.

Lemma independent_execution : forall pr1 pr2 pr,
  lstepSilent^* (pr1 || pr2) pr
  -> (forall ch, mayTouch pr1 ch -> mayTouch pr2 ch -> False)
  -> exists pr1' pr2', pr = pr1' || pr2'
                       /\ lstepSilent^* pr1 pr1'
                       /\ lstepSilent^* pr2 pr2'.
Proof.
  induct 1; simplify; eauto.
  invert H.
  
  specialize (IHtrc _ _ eq_refl).
  match type of IHtrc with
  | ?P -> _ => assert P by eauto
  end.
  first_order.
  eauto 10.

  specialize (IHtrc _ _ eq_refl).
  match type of IHtrc with
  | ?P -> _ => assert P by eauto
  end.
  first_order.
  eauto 10.

  exfalso; eauto.

  exfalso; eauto.
Qed.

Theorem independently_deadlock_free : forall pr1 pr2,
    invariantFor (trsys_of pr1)
                 (fun pr => inert pr
                            \/ exists pr', lstep pr Silent pr')
    -> invariantFor (trsys_of pr2)
                    (fun pr => inert pr
                               \/ exists pr', lstep pr Silent pr')
    -> (forall ch, mayTouch pr1 ch -> mayTouch pr2 ch -> False)
    -> invariantFor (trsys_of (pr1 || pr2))
                    (fun pr => inert pr
                               \/ exists pr', lstep pr Silent pr').
Proof.
  unfold invariantFor; simplify.
  propositional; subst.
  apply independent_execution in H3; auto.
  first_order; subst.
  apply H in H3; apply H0 in H4; auto.
  first_order; eauto.
Qed.

Ltac NoDup :=
  repeat match goal with
         | [ H : NoDup _ |- _ ] => invert H
         end; simplify.

Ltac mayTouch :=
  match goal with
  | [ H : mayTouch (match ?E with _ => _ end) _ |- _ ] => cases E
  | [ H : mayTouch _ _ |- _ ] => invert H; try solve [ equality ]
  end.

Example online_store_no_deadlock' : forall k input output
                                           product payment_info payment_checker in_stock
                                           add_review payment_success send_payment_info
                                           in_stock_or_not request_product
                                           merchant_to_warehouse warehouse_to_merchant,
  NoDup [input; output;
           request_product; in_stock_or_not; send_payment_info; payment_success; add_review;
             merchant_to_warehouse; warehouse_to_merchant]
    -> invariantFor (trsys_of ((addN k input output
                                || add2_client input output)
                               || ((customer' request_product in_stock_or_not
                                              send_payment_info payment_success add_review
                                              product payment_info
                                    || (merchant' request_product in_stock_or_not
                                                  send_payment_info payment_success add_review
                                                  merchant_to_warehouse
                                                  warehouse_to_merchant payment_checker
                                        || (warehouse merchant_to_warehouse
                                                      warehouse_to_merchant
                                                      in_stock || Done))))))
                    (fun pr => inert pr
                               \/ exists pr', lstep pr Silent pr').
Proof.
  simplify.
  eapply independently_deadlock_free.

  eapply invariant_weaken.
  apply adding_no_deadlock.
  NoDup; equality.
  simplify.
  first_order; subst; eauto.

  apply online_store_no_deadlock'.
  NoDup; repeat constructor; simplify; equality.

  simplify.
  NoDup; propositional.
  generalize dependent H1.
  repeat mayTouch; intro; repeat mayTouch.
Qed.
