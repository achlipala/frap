(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 15: Pi-Calculus and Behavioral Refinement
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap Eqdep FunctionalExtensionality.

Set Implicit Arguments.
Set Asymmetric Patterns.

Ltac invert H := (Frap.invert H || (inversion H; clear H));
                repeat match goal with
                       | [ x : _ |- _ ] => subst x
                       | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; try subst
                       end.


Notation channel := nat (only parsing).

Inductive proc :=
| NewChannel (notThese : list channel) (k : channel -> proc)
| Send (ch : channel) {A : Set} (v : A) (k : proc)
| Recv (ch : channel) {A : Set} (k : A -> proc)
| Par (pr1 pr2 : proc)
| Dup (pr : proc)
| Done
| Fail.

Notation pid := nat (only parsing).
Notation procs := (fmap pid proc).
Notation channels := (set channel).

Notation "'New' ls ( x ) ; k" := (NewChannel ls (fun x => k)) (right associativity, at level 45, ls at level 0).
Notation "!! ch ( v ) ; k" := (Send ch v k) (right associativity, at level 45, ch at level 0).
Notation "?? ch ( x : T ) ; k" := (Recv ch (fun x : T => k)) (right associativity, at level 45, ch at level 0, x at level 0).
Infix "||" := Par.


(** * Example *)

Definition simple_addN (k : nat) (input output : channel) : proc :=
  Dup (??input(n : nat);
       !!output(n + k);
       Done).

Definition add2 (input output : channel) : proc :=
  New[input;output](intermediate);
  (simple_addN 1 input intermediate
   || simple_addN 1 intermediate output).

Definition tester (k n : nat) (input output : channel) : proc :=
  !!input(n);
  ??output(n' : nat);
  if n' ==n (n + k) then
    Done
  else
    Fail.


(** * Flat semantics *)

Inductive step : procs -> procs -> Prop :=
| StepNew : forall chs ps i k ch,
    ps $? i = Some (NewChannel chs k)
    -> ~List.In ch chs
    -> step ps (ps $+ (i, k ch))
| StepSendRecv : forall ps i ch {A : Set} (v : A) k1 j k2,
    ps $? i = Some (Send ch v k1)
    -> ps $? j = Some (Recv ch k2)
    -> step ps (ps $+ (i, k1) $+ (j, k2 v))
| StepPar : forall ps i pr1 pr2 j,
    ps $? i = Some (Par pr1 pr2)
    -> ps $? j = None
    -> step ps (ps $+ (i, pr1) $+ (j, pr2))
| StepDup : forall ps i pr j,
    ps $? i = Some (Dup pr)
    -> ps $? j = None
    -> step ps (ps $+ (i, Dup pr) $+ (j, pr)).


(** * Labeled semantics *)

Record message := {
  Channel : channel;
  TypeOf : Set;
  Value : TypeOf
}.

Inductive action :=
| Output (m : message)
| Input (m : message).

Inductive label :=
| Silent
| Action (a : action).

Coercion Action : action >-> label.

Inductive lstep : proc -> label -> proc -> Prop :=
| LStepSend : forall ch {A : Set} (v : A) k,
    lstep (Send ch v k)
          (Output {| Channel := ch; Value := v |})
          k
| LStepRecv : forall ch {A : Set} (k : A -> _) v,
    lstep (Recv ch k)
          (Input {| Channel := ch; Value := v |})
          (k v)
| LStepDup : forall pr,
    lstep (Dup pr) Silent (Par (Dup pr) pr)
| LStepNewInside : forall chs k l k',
    (forall ch, ~List.In ch chs -> lstep (k ch) l (k' ch))
    -> lstep (NewChannel chs k) l (NewChannel chs k')
| LStepPar1 : forall pr1 pr2 l pr1',
    lstep pr1 l pr1'
    -> lstep (Par pr1 pr2) l (Par pr1' pr2)
| LStepPar2 : forall pr1 pr2 l pr2',
    lstep pr2 l pr2'
    -> lstep (Par pr1 pr2) l (Par pr1 pr2')
| LStepRendezvousLeft : forall pr1 ch {A : Set} (v : A) pr1' pr2 pr2',
    lstep pr1 (Input {| Channel := ch; Value := v |}) pr1'
    -> lstep pr2 (Output {| Channel := ch; Value := v |}) pr2'
    -> lstep (Par pr1 pr2) Silent (Par pr1' pr2')
| LStepRendezvousRight : forall pr1 ch {A : Set} (v : A) pr1' pr2 pr2',
    lstep pr1 (Output {| Channel := ch; Value := v |}) pr1'
    -> lstep pr2 (Input {| Channel := ch; Value := v |}) pr2'
    -> lstep (Par pr1 pr2) Silent (Par pr1' pr2').

Inductive couldGenerate : proc -> list action -> Prop :=
| CgNothing : forall pr,
    couldGenerate pr []
| CgSilent : forall pr pr' tr,
    lstep pr Silent pr'
    -> couldGenerate pr' tr
    -> couldGenerate pr tr
| CgAction : forall pr a pr' tr,
    lstep pr (Action a) pr'
    -> couldGenerate pr' tr
    -> couldGenerate pr (a :: tr).

Definition lstepSilent (pr1 pr2 : proc) := lstep pr1 Silent pr2.

Definition simulates (R : proc -> proc -> Prop) (pr1 pr2 : proc) :=
  (forall pr1 pr2, R pr1 pr2
                   -> forall pr1', lstepSilent pr1 pr1'
                                   -> exists pr2', lstepSilent^* pr2 pr2'
                                                   /\ R pr1' pr2')
  /\ (forall pr1 pr2, R pr1 pr2
                      -> forall a pr1', lstep pr1 (Action a) pr1'
                                        -> exists pr2' pr2'', lstepSilent^* pr2 pr2'
                                                              /\ lstep pr2' (Action a) pr2''
                                                              /\ R pr1' pr2'')
  /\ R pr1 pr2.

Definition refines (pr1 pr2 : proc) :=
  exists R, simulates R pr1 pr2.

Infix "<|" := refines (no associativity, at level 70).


(** * Simulation: a proof method *)

Hint Constructors couldGenerate.

Lemma lstepSilent_couldGenerate : forall pr1 pr2,
  lstepSilent^* pr1 pr2
  -> forall tr, couldGenerate pr2 tr
                -> couldGenerate pr1 tr.
Proof.
  induct 1; eauto.
Qed.

Hint Resolve lstepSilent_couldGenerate.

Lemma simulates_couldGenerate' : forall (R : proc -> proc -> Prop),
    (forall pr1 pr2, R pr1 pr2
                     -> forall pr1', lstepSilent pr1 pr1'
                                     -> exists pr2', lstepSilent^* pr2 pr2'
                                                     /\ R pr1' pr2')
    -> (forall pr1 pr2, R pr1 pr2
                        -> forall a pr1', lstep pr1 (Action a) pr1'
                                          -> exists pr2' pr2'', lstepSilent^* pr2 pr2'
                                                                /\ lstep pr2' (Action a) pr2''
                                                                /\ R pr1' pr2'')
    -> forall pr1 tr, couldGenerate pr1 tr
                      -> forall pr2, R pr1 pr2
                                     -> couldGenerate pr2 tr.
Proof.
  induct 3; simplify; auto.

  eapply H in H1; eauto.
  first_order.
  eauto.

  eapply H0 in H1; eauto.
  first_order.
  eauto.
Qed.

Theorem simulates_couldGenerate : forall pr1 pr2, pr1 <| pr2
    -> forall tr, couldGenerate pr1 tr
                  -> couldGenerate pr2 tr.
Proof.
  unfold refines; first_order; eauto using simulates_couldGenerate'.
Qed.


(** * Tactics for automating refinement proofs *)

Lemma invert_Recv : forall ch (A : Set) (k : A -> proc) (x : A) pr,
    lstep (Recv ch k) (Input {| Channel := ch; Value := x |}) pr
    -> pr = k x.
Proof.
  invert 1; auto.
Qed.

Ltac inverter :=
  repeat match goal with
         | [ H : lstep _ _ _ |- _ ] => (apply invert_Recv in H; try subst) || invert H
         | [ H : lstepSilent _ _ |- _ ] => invert H
         end.

Hint Constructors lstep.

Definition In' := In.
Theorem In'_eq : In' = In.
Proof.
  auto.
Qed.

Opaque In.

Ltac instWith n := 
  match goal with
  | [ H0 : forall ch, ~In ch ?ls -> _, H : forall ch, ~In ch ?ls -> lstep _ _ _ |- _ ] =>
    let Hni := fresh "Hni" in let Hni' := fresh "Hni'" in
    assert (Hni : ~In n ls) by (rewrite <- In'_eq in *; simplify; propositional; linear_arithmetic);
    assert (Hni' : ~In (S n) ls) by (rewrite <- In'_eq in *; simplify; propositional; linear_arithmetic);
      generalize (H0 _ Hni), (H _ Hni), (H0 _ Hni'), (H _ Hni'); simplify;
      repeat match goal with
             | [ H : ?k _ = _, H' : lstep (?k _) _ _ |- _ ] => rewrite H in H'
             end; inverter; try linear_arithmetic
  | [ H0 : forall ch, ~In ch ?ls -> _, H : forall ch, ~In ch ?ls -> lstep _ _ _ |- _ ] =>
    let Hni := fresh "Hni" in
    assert (Hni : ~In n ls) by (rewrite <- In'_eq in *; simplify; propositional; linear_arithmetic);
      generalize (H0 _ Hni), (H _ Hni); simplify;
      repeat match goal with
             | [ H : ?k _ = _, H' : lstep (?k _) _ _ |- _ ] => rewrite H in H'
             end; inverter
  | [ H : forall ch, ~In ch ?ls -> lstep _ _ _ |- _ ] =>
    let Hni := fresh "Hni" in
    assert (Hni : ~In n ls) by (rewrite <- In'_eq in *; simplify; propositional; linear_arithmetic);
      generalize (H _ Hni); simplify; inverter
  end.

Ltac impossible := 
  match goal with
  | [ H : forall ch, ~In ch ?ls -> _ |- _ ] =>
    instWith (S (fold_left max ls 0))
  end.

Ltac inferAction :=
  match goal with
  | [ H : forall ch, ~In ch ?ls -> lstep _ (Action ?a) _ |- _ ] =>
    let av := fresh "av" in
    evar (av : action);
    let av' := eval unfold av in av in
    clear av;
    assert (a = av'); [ instWith (S (fold_left max ls 0));
                        match goal with
                        | [ |- ?X = _ ] => instantiate (1 := X)
                        end; reflexivity | subst ]
  end.

Ltac inferProc :=
  match goal with
  | [ H : forall ch, ~In ch ?ls -> lstep _ _ (?k' ch) |- _ ] =>
    let k'' := fresh "k''" in
    evar (k'' : channel -> proc);
    let k''' := eval unfold k'' in k'' in
    clear k'';
    assert (forall ch, ~In ch ls
                       -> k' ch = k''' ch);
    [ intro ch; simplify; instWith ch; simplify; inverter;
      (reflexivity || rewrite <- In'_eq in *; simplify; propositional) | subst; simplify ]
  end.

Ltac inferRead :=
  match goal with
  | [ _ : forall ch, ~In ch ?ls -> lstep _ (Action ?a) _ |- _ ] =>
    let ch0 := fresh "ch0" in
    evar (ch0 : channel);
    let ch0' := eval unfold ch0 in ch0 in
    clear ch0;
    assert (exists v : nat, a = Input {| Channel := ch0'; Value := v |})
           by (instWith (S (fold_left max ls 0)); eauto);
      first_order; subst
  end.


(** * Examples *)

Module Example1.
  Definition simple_addN_once (k : nat) (input output : channel) : proc :=
    ??input(n : nat);
    !!output(n + k);
    Done.

  Definition add2_once (input output : channel) : proc :=
    New[input;output](intermediate);
    (simple_addN_once 1 input intermediate
     || simple_addN_once 1 intermediate output).

  Inductive R_add2 (input output : channel) : proc -> proc -> Prop :=
  | Initial : forall k,
      (forall ch, ~List.In ch [input; output]
                  -> k ch = ??input(n : nat); !!ch(n + 1); Done || simple_addN_once 1 ch output)
      -> R_add2 input output
             (NewChannel [input;output] k)
             (simple_addN_once 2 input output)
  | GotInput : forall n k,
      (forall ch, ~List.In ch [input; output]
                  -> k ch = !!ch(n + 1); Done || simple_addN_once 1 ch output)
      -> R_add2 input output
                (NewChannel [input;output] k)
                (!!output(n + 2); Done)
  | HandedOff : forall n k,
      (forall ch, ~List.In ch [input; output]
                  -> k ch = Done || (!!output(n + 2); Done))
      -> R_add2 input output
                (NewChannel [input;output] k)
                (!!output(n + 2); Done)
  | Finished : forall k,
      (forall ch, ~List.In ch [input; output]
                  -> k ch = Done || Done)
      -> R_add2 input output
                (NewChannel [input;output] k)
                Done.

  Hint Constructors R_add2.

  Theorem add2_once_refines_simple_addN_once : forall input output,
      add2_once input output <| simple_addN_once 2 input output.
  Proof.
    simplify.
    exists (R_add2 input output).
    unfold simulates; propositional.

    invert H; simplify; inverter.
    impossible.
    inferProc.
    replace (n + 1 + 1) with (n + 2) in * by linear_arithmetic.
    eauto.
    impossible.
    impossible.

    invert H; simplify; inverter.
    inferRead.
    inferProc.
    unfold simple_addN_once; eauto 10.
    impossible.
    inferAction.
    inferProc.
    eauto 10.
    impossible.

    unfold add2_once; eauto.
  Qed.
End Example1.


(** * Compositional reasoning principles *)

(** ** Dup *)

Inductive RDup (R : proc -> proc -> Prop) : proc -> proc -> Prop :=
| RDupLeaf : forall pr1 pr2,
    R pr1 pr2 
    -> RDup R pr1 pr2
| RDupDup : forall pr1 pr2,
    RDup R pr1 pr2
    -> RDup R (Dup pr1) (Dup pr2)
| RDupPar : forall pr1 pr2 pr1' pr2',
    RDup R pr1 pr1'
    -> RDup R pr2 pr2'
    -> RDup R (Par pr1 pr2) (Par pr1' pr2').

Hint Constructors RDup.

Hint Unfold lstepSilent.

Lemma lstepSilent_Par1 : forall pr1 pr1' pr2,
    lstepSilent^* pr1 pr1'
    -> lstepSilent^* (Par pr1 pr2) (Par pr1' pr2).
Proof.
  induct 1; eauto.
Qed.

Lemma lstepSilent_Par2 : forall pr2 pr2' pr1,
    lstepSilent^* pr2 pr2'
    -> lstepSilent^* (Par pr1 pr2) (Par pr1 pr2').
Proof.
  induct 1; eauto.
Qed.

Hint Resolve lstepSilent_Par1 lstepSilent_Par2.

Lemma refines_Dup_Action : forall R : _ -> _ -> Prop,
    (forall pr1 pr2, R pr1 pr2
                     -> forall pr1' a, lstep pr1 (Action a) pr1'
                                     -> exists pr2' pr2'', lstepSilent^* pr2 pr2'
                                                           /\ lstep pr2' (Action a) pr2''
                                                           /\ R pr1' pr2'')
    -> forall pr1 pr2, RDup R pr1 pr2
                       -> forall pr1' a, lstep pr1 (Action a) pr1'
                                       -> exists pr2' pr2'', lstepSilent^* pr2 pr2'
                                                             /\ lstep pr2' (Action a) pr2''
                                                             /\ RDup R pr1' pr2''.
Proof.
  induct 2; simplify.

  eapply H in H1; eauto.
  first_order.
  eauto 6.

  invert H1.

  invert H0.
  apply IHRDup1 in H5.
  first_order.
  eauto 10.
  apply IHRDup2 in H5.
  first_order.
  eauto 10.
Qed.

Lemma refines_Dup_Silent : forall R : _ -> _ -> Prop,
    (forall pr1 pr2, R pr1 pr2
                     -> forall pr1', lstepSilent pr1 pr1'
                                     -> exists pr2', lstepSilent^* pr2 pr2'
                                                     /\ R pr1' pr2')
    -> (forall pr1 pr2, R pr1 pr2
                        -> forall pr1' a, lstep pr1 (Action a) pr1'
                                          -> exists pr2' pr2'', lstepSilent^* pr2 pr2'
                                                                /\ lstep pr2' (Action a) pr2''
                                                                /\ R pr1' pr2'')
    -> forall pr1 pr2, RDup R pr1 pr2
                       -> forall pr1', lstepSilent pr1 pr1'
                                       -> exists pr2', lstepSilent^* pr2 pr2' /\ RDup R pr1' pr2'.
Proof.
  induct 3; simplify.

  eapply H in H1; eauto.
  first_order.
  eauto.

  invert H2.
  eauto 10.

  invert H1.
  apply IHRDup1 in H6.
  first_order.
  eauto.
  apply IHRDup2 in H6.
  first_order.
  eauto.
  eapply refines_Dup_Action in H4; eauto.
  eapply refines_Dup_Action in H5; eauto.
  first_order.
  eexists; propositional.
  apply trc_trans with (x1 || pr2').
  eauto.
  apply trc_trans with (x1 || x).
  eauto.
  apply trc_one.
  eauto.
  eauto.
  eapply refines_Dup_Action in H4; eauto.
  eapply refines_Dup_Action in H5; eauto.
  first_order.
  eexists; propositional.
  apply trc_trans with (x1 || pr2').
  eauto.
  apply trc_trans with (x1 || x).
  eauto.
  apply trc_one.
  eauto.
  eauto.
Qed.

Theorem refines_Dup : forall pr1 pr2,
    pr1 <| pr2
    -> Dup pr1 <| Dup pr2.
Proof.
  invert 1.
  exists (RDup x).
  unfold simulates in *.
  propositional; eauto using refines_Dup_Silent, refines_Dup_Action.
Qed.
