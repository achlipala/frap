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
| Done.

Notation pid := nat (only parsing).
Notation procs := (fmap pid proc).
Notation channels := (set channel).

Notation "'New' ls ( x ) ; k" := (NewChannel ls (fun x => k)) (right associativity, at level 51, ls at level 0).
Notation "!! ch ( v ) ; k" := (Send ch v k) (right associativity, at level 45, ch at level 0).
Notation "?? ch ( x : T ) ; k" := (Recv ch (fun x : T => k)) (right associativity, at level 45, ch at level 0, x at level 0).
Infix "||" := Par.


(** * Example *)

Definition addN (k : nat) (input output : channel) : proc :=
  ??input(n : nat);
  !!output(n + k);
  Done.

Definition addNs (k : nat) (input output : channel) : proc :=
  Dup (addN k input output).

Definition add2 (input output : channel) : proc :=
  Dup (New[input;output](intermediate);
        addN 1 input intermediate
        || addN 1 intermediate output).

Definition tester (metaInput input output metaOutput : channel) : proc :=
  ??metaInput(n : nat);
  !!input(n * 2);
  ??output(r : nat);
  !!metaOutput(r);
  Done.


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
  Definition add2_once (input output : channel) : proc :=
    New[input;output](intermediate);
    (addN 1 input intermediate
     || addN 1 intermediate output).

  Inductive R_add2 (input output : channel) : proc -> proc -> Prop :=
  | Initial : forall k,
      (forall ch, ~List.In ch [input; output]
                  -> k ch = ??input(n : nat); !!ch(n + 1); Done || addN 1 ch output)
      -> R_add2 input output
             (NewChannel [input;output] k)
             (addN 2 input output)
  | GotInput : forall n k,
      (forall ch, ~List.In ch [input; output]
                  -> k ch = !!ch(n + 1); Done || addN 1 ch output)
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

  Theorem add2_once_refines_addN : forall input output,
      add2_once input output <| addN 2 input output.
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
    unfold addN; eauto 10.
    impossible.
    inferAction.
    inferProc.
    eauto 10.
    impossible.

    unfold add2_once; eauto.
  Qed.
End Example1.


(** * Compositional reasoning principles *)

Theorem refines_refl : forall pr,
    pr <| pr.
Proof.
  simplify.
  exists (fun pr1 pr2 => pr1 = pr2).
  first_order; subst; eauto.
Qed.

Lemma refines_trans' : forall R : _ -> _ -> Prop,
    (forall pr1 pr2,
        R pr1 pr2
        -> forall pr1', lstepSilent pr1 pr1'
                        -> exists pr2', lstepSilent^* pr2 pr2' /\ R pr1' pr2')
    -> forall pr1 pr1', lstepSilent^* pr1 pr1'
    -> forall pr2, R pr1 pr2
    -> exists pr2', R pr1' pr2' /\ lstepSilent^* pr2 pr2'.
Proof.
  induct 2; simplify; eauto.

  eapply H in H0; eauto.
  first_order.
  apply IHtrc in H3.
  first_order.
  eauto using trc_trans.
Qed.

Theorem refines_trans : forall pr1 pr2 pr3,
    pr1 <| pr2
    -> pr2 <| pr3
    -> pr1 <| pr3.
Proof.
  invert 1; invert 1.
  exists (fun p q => exists r, x p r /\ x0 r q).
  first_order.

  eapply H0 in H5; eauto.
  first_order.
  eapply refines_trans' in H7; eauto.
  first_order.

  eapply H3 in H6; eauto.
  first_order.
  eapply refines_trans' in H7; eauto.
  first_order.
  eapply H1 in H8; eauto.
  first_order.
  eauto 8 using trc_trans.
Qed.


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

(** ** Par *)

Inductive RPar (R1 R2 : proc -> proc -> Prop) : proc -> proc -> Prop :=
| RPar1 : forall pr1 pr2 pr1' pr2',
    R1 pr1 pr1'
    -> R2 pr2 pr2'
    -> RPar R1 R2 (pr1 || pr2) (pr1' || pr2').

Hint Constructors RPar.

Lemma refines_Par_Action : forall R1 R2 : _ -> _ -> Prop,
    (forall pr1 pr2, R1 pr1 pr2
                     -> forall pr1' a, lstep pr1 (Action a) pr1'
                                     -> exists pr2' pr2'', lstepSilent^* pr2 pr2'
                                                           /\ lstep pr2' (Action a) pr2''
                                                           /\ R1 pr1' pr2'')
    -> (forall pr1 pr2, R2 pr1 pr2
                        -> forall pr1' a, lstep pr1 (Action a) pr1'
                                          -> exists pr2' pr2'', lstepSilent^* pr2 pr2'
                                                                /\ lstep pr2' (Action a) pr2''
                                                                /\ R2 pr1' pr2'')
    -> forall pr1 pr2, RPar R1 R2 pr1 pr2
                       -> forall pr1' a, lstep pr1 (Action a) pr1'
                                       -> exists pr2' pr2'', lstepSilent^* pr2 pr2'
                                                             /\ lstep pr2' (Action a) pr2''
                                                             /\ RPar R1 R2 pr1' pr2''.
Proof.
  invert 3; simplify.

  invert H1.
  eapply H in H8; eauto.
  first_order.
  eauto 10.
  eapply H0 in H8; eauto.
  first_order.
  eauto 10.
Qed.

Lemma refines_Par_Silent : forall R1 R2 : _ -> _ -> Prop,
    (forall pr1 pr2, R1 pr1 pr2
                     -> forall pr1', lstepSilent pr1 pr1'
                                     -> exists pr2', lstepSilent^* pr2 pr2'
                                                     /\ R1 pr1' pr2')
    -> (forall pr1 pr2, R1 pr1 pr2
                        -> forall pr1' a, lstep pr1 (Action a) pr1'
                                          -> exists pr2' pr2'', lstepSilent^* pr2 pr2'
                                                                /\ lstep pr2' (Action a) pr2''
                                                                /\ R1 pr1' pr2'')
    -> (forall pr1 pr2, R2 pr1 pr2
                     -> forall pr1', lstepSilent pr1 pr1'
                                     -> exists pr2', lstepSilent^* pr2 pr2'
                                                     /\ R2 pr1' pr2')
    -> (forall pr1 pr2, R2 pr1 pr2
                        -> forall pr1' a, lstep pr1 (Action a) pr1'
                                          -> exists pr2' pr2'', lstepSilent^* pr2 pr2'
                                                                /\ lstep pr2' (Action a) pr2''
                                                                /\ R2 pr1' pr2'')
    -> forall pr1 pr2, RPar R1 R2 pr1 pr2
                       -> forall pr1', lstepSilent pr1 pr1'
                                       -> exists pr2', lstepSilent^* pr2 pr2' /\ RPar R1 R2 pr1' pr2'.
Proof.
  invert 5; simplify.

  invert H3.
  eapply H in H10; eauto.
  first_order; eauto.
  eapply H1 in H10; eauto.
  first_order; eauto.
  eapply H0 in H8; eauto.
  eapply H2 in H9; eauto.
  first_order.
  eexists; propositional.
  apply trc_trans with (x1 || pr2').
  eauto.
  apply trc_trans with (x1 || x).
  eauto.
  apply trc_one.
  eauto.
  eauto.
  eapply H0 in H8; eauto.
  eapply H2 in H9; eauto.
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

Theorem refines_Par : forall pr1 pr2 pr1' pr2',
    pr1 <| pr1'
    -> pr2 <| pr2'
    -> pr1 || pr2 <| pr1' || pr2'.
Proof.
  invert 1; invert 1.
  exists (RPar x x0).
  unfold simulates in *.
  propositional; eauto using refines_Par_Silent, refines_Par_Action.
Qed.


(** * Example again *)

Theorem refines_add2 : forall input output,
    add2 input output <| addNs 2 input output.
Proof.
  simplify.
  apply refines_Dup.
  apply Example1.add2_once_refines_addN.
Qed.

Theorem refines_add2_with_tester : forall metaInput input output metaOutput,
    add2 input output || tester metaInput input output metaOutput
         <| addNs 2 input output || tester metaInput input output metaOutput.
Proof.
  simplify.
  apply refines_Par.
  apply refines_add2.
  apply refines_refl.
Qed.


(** * Tree membership *)

Inductive tree :=
| Leaf (n : nat)
| Node (l r : tree).

Fixpoint mem (n : nat) (t : tree) : bool :=
  match t with
  | Leaf m => if m ==n n then true else false
  | Node l r => mem n l || mem n r
  end%bool.

Definition inTree_seq (t : tree) (input output : channel) :=
  Dup (??input(n : nat);
       if mem n t then
         !!output(tt);
         Done
       else
         Done).

Fixpoint inTree_par' (n : nat) (t : tree) (output : channel) :=
  match t with
  | Leaf m =>
    if m ==n n then
      !!output(tt);
      Done
    else
      Done
  | Node l r =>
    inTree_par' n l output || inTree_par' n r output
  end.

Definition inTree_par (t : tree) (input output : channel) :=
  Dup (??input(n : nat);
       New[input;output](output');
       inTree_par' n t output'
       || ??output'(_ : unit);
          !!output(tt);
          Done).

Inductive TreeThreads (output' : channel) : bool -> proc -> Prop :=
| TtDone : forall maySend,
    TreeThreads output' maySend Done
| TtSend :
    TreeThreads output' true (!!output'(tt); Done)
| TtPar : forall maySend pr1 pr2,
    TreeThreads output' maySend pr1
    -> TreeThreads output' maySend pr2
    -> TreeThreads output' maySend (pr1 || pr2).

Inductive RTree (t : tree) (input output : channel) : proc -> proc -> Prop :=
| TreeInit :
    RTree t input output
          (??input(n : nat);
           New[input;output](output');
           inTree_par' n t output'
           || ??output'(_ : unit);
           !!output(tt);
           Done)
          (??input(n : nat);
           if mem n t then
             !!output(tt);
             Done
           else
             Done)
| TreeSearching : forall n k threads,
    (forall ch, ~In ch [input; output]
                -> k ch = threads ch
                          || ??ch(_ : unit);
                !!output(tt);
                Done)
    -> (forall ch, ~In ch [input; output]
                   -> TreeThreads ch (mem n t) (threads ch))
    -> RTree t input output
          (NewChannel [input;output] k)
          (if mem n t then
             !!output(tt);
             Done
           else
             Done)
| TreeFound : forall n k threads,
    mem n t = true
    -> (forall ch, ~In ch [input; output]
                   -> k ch = threads ch
                             || !!output(tt);
                                Done)
    -> (forall ch, ~In ch [input; output]
                   -> TreeThreads ch true (threads ch))
    -> RTree t input output
          (NewChannel [input;output] k)
          (!!output(tt);
           Done)
| TreeNotified : forall n k threads,
    mem n t = true
    -> (forall ch, ~In ch [input; output]
                   -> k ch = threads ch
                             || Done)
    -> (forall ch, ~In ch [input; output]
                   -> TreeThreads ch true (threads ch))
    -> RTree t input output
          (NewChannel [input;output] k)
          Done.

Hint Constructors TreeThreads RTree.

Lemma TreeThreads_actionIs : forall ch maySend pr,
    TreeThreads ch maySend pr
    -> forall a pr', lstep pr (Action a) pr'
                   -> a = Output {| Channel := ch; Value := tt |}.
Proof.
  induct 1; invert 1; eauto.
Qed.

Lemma TreeThreads_silent : forall ch maySend pr,
    TreeThreads ch maySend pr
    -> forall pr', lstep pr Silent pr'
                   -> False.
Proof.
  induct 1; invert 1; simplify; eauto.

  eapply TreeThreads_actionIs in H4; eauto.
  equality.

  eapply TreeThreads_actionIs in H5; eauto.
  equality.
Qed.

Lemma TreeThreads_maySend : forall ch maySend pr,
    TreeThreads ch maySend pr
    -> forall a pr', lstep pr a pr'
                     -> maySend = true.
Proof.
  induct 1; invert 1; eauto.
Qed.

Lemma TreeThreads_action : forall ch maySend pr,
    TreeThreads ch maySend pr
    -> forall a pr', lstep pr a pr'
                     -> TreeThreads ch maySend pr'.
Proof.
  induct 1; invert 1; eauto.
Qed.

Lemma TreeThreads_weaken : forall ch maySend pr,
    TreeThreads ch maySend pr
    -> TreeThreads ch true pr.
Proof.
  induct 1; eauto.
Qed.

Hint Resolve TreeThreads_silent TreeThreads_maySend TreeThreads_action TreeThreads_weaken.

Lemma TreeThreads_inTree_par' : forall n ch t,
    TreeThreads ch (mem n t) (inTree_par' n t ch).
Proof.
  induct t; simplify; eauto.
  cases (n0 ==n n); eauto.
  cases (mem n t1); simplify; eauto.
  cases (mem n t2); simplify; eauto.
Qed.

Hint Resolve TreeThreads_inTree_par'.

Definition firstThread (p : proc) : proc :=
  match p with
  | Par p1 _ => p1
  | _ => Done
  end.

Theorem refines_inTree_par : forall t input output,
    inTree_par t input output <| inTree_seq t input output.
Proof.
  simplify.
  apply refines_Dup.
  exists (RTree t input output).
  first_order; eauto.

  invert H; inverter.

  assert (mem n t = true).
  assert (~In (S (max input output)) [input; output]) by (rewrite <- In'_eq; simplify; propositional; linear_arithmetic).
  specialize (H1 _ H).
  specialize (H6 _ H).
  rewrite H1 in H6.
  invert H6; eauto.
  invert H5.
  rewrite H.
  eexists; propositional; eauto.
  eapply TreeFound with (threads := fun ch => firstThread (k' ch)); eauto.
  simplify.
  specialize (H1 _ H0).
  specialize (H6 _ H0).
  specialize (H2 _ H0).
  rewrite H1 in H6.
  invert H6.
  exfalso; eauto.
  invert H7.
  specialize (TreeThreads_actionIs H2 H7); invert 1.
  specialize (TreeThreads_actionIs H2 H7); invert 1.
  invert H8.
  reflexivity.
  simplify.
  specialize (H1 _ H0).
  specialize (H6 _ H0).
  specialize (H2 _ H0).
  rewrite H1 in H6.
  invert H6; eauto.

  exfalso.
  assert (~In (S (max input output)) [input; output]) by (rewrite <- In'_eq; simplify; propositional; linear_arithmetic).
  specialize (H2 _ H).
  specialize (H7 _ H).
  specialize (H3 _ H).
  rewrite H2 in H7.
  invert H7; eauto.
  specialize (TreeThreads_actionIs H3 H6); invert 1.
  specialize (TreeThreads_actionIs H3 H6); invert 1.
  invert H8.

  eexists; propositional; eauto.
  eapply TreeNotified with (threads := fun ch => firstThread (k' ch)); eauto.
  simplify.
  specialize (H2 _ H).
  specialize (H3 _ H).
  specialize (H7 _ H).
  rewrite H2 in H7.
  invert H7; eauto.
  invert H6.
  invert H8.
  invert H8.
  simplify.
  specialize (H2 _ H).
  specialize (H3 _ H).
  specialize (H7 _ H).
  rewrite H2 in H7.
  invert H7; eauto.

  invert H; inverter; eauto 6.

  exfalso.
  assert (~In (S (max input output)) [input; output]) by (rewrite <- In'_eq; simplify; propositional; linear_arithmetic).
  generalize (H1 _ H).
  generalize (H2 _ H).
  generalize (H6 _ H).
  simplify.
  rewrite H4 in H0.
  invert H0.
  specialize (TreeThreads_actionIs H3 H9); simplify; subst.
  assert (~In (S (S (max input output))) [input; output]) by (rewrite <- In'_eq; simplify; propositional; linear_arithmetic).
  specialize (H1 _ H0).
  specialize (H2 _ H0).
  specialize (H6 _ H0).
  rewrite H1 in H6.
  invert H6.
  specialize (TreeThreads_actionIs H2 H11); invert 1; linear_arithmetic.
  invert H11.
  invert H9.
  assert (~In (S (S (max input output))) [input; output]) by (rewrite <- In'_eq; simplify; propositional; linear_arithmetic).
  specialize (H1 _ H0).
  specialize (H2 _ H0).
  specialize (H6 _ H0).
  rewrite H1 in H6.
  invert H6.
  specialize (TreeThreads_actionIs H2 H9); invert 1; linear_arithmetic.
  invert H9; linear_arithmetic.

  assert (a = Output {| Channel := output; Value := tt |}).
  assert (~In (S (max input output)) [input; output]) by (rewrite <- In'_eq; simplify; propositional; linear_arithmetic).  
  generalize (H2 _ H).
  generalize (H3 _ H).
  generalize (H7 _ H).
  simplify.
  rewrite H5 in H0.
  invert H0.
  exfalso.
  specialize (TreeThreads_actionIs H4 H10); simplify; subst.
  assert (~In (S (S (max input output))) [input; output]) by (rewrite <- In'_eq; simplify; propositional; linear_arithmetic).
  generalize (H2 _ H0).
  generalize (H3 _ H0).
  generalize (H7 _ H0).
  simplify.
  rewrite H9 in H6.
  invert H6.
  specialize (TreeThreads_actionIs H8 H15); invert 1; linear_arithmetic.
  invert H15; linear_arithmetic.
  invert H10; auto.
  subst.
  do 2 eexists; propositional; eauto.
  eapply TreeNotified with (threads := fun ch => firstThread (k' ch)); eauto.
  simplify.
  generalize (H2 _ H).
  generalize (H3 _ H).
  generalize (H7 _ H).
  simplify.
  rewrite H5 in H0.
  invert H0.
  specialize (TreeThreads_actionIs H4 H10); invert 1.
  rewrite <- In'_eq in *; simplify; propositional.
  invert H10.
  reflexivity.
  simplify.
  generalize (H2 _ H).
  generalize (H3 _ H).
  generalize (H7 _ H).
  simplify.
  rewrite H5 in H0.
  invert H0; eauto.

  exfalso.
  assert (~In (S (max input output)) [input; output]) by (rewrite <- In'_eq; simplify; propositional; linear_arithmetic).  
  generalize (H2 _ H).
  generalize (H3 _ H).
  generalize (H7 _ H).
  simplify.
  rewrite H5 in H0.
  invert H0.
  specialize (TreeThreads_actionIs H4 H10); invert 1.
  assert (~In (S (S (max input output))) [input; output]) by (rewrite <- In'_eq; simplify; propositional; linear_arithmetic).  
  generalize (H2 _ H0).
  generalize (H3 _ H0).
  generalize (H7 _ H0).
  simplify.
  rewrite H9 in H6.
  invert H6.
  specialize (TreeThreads_actionIs H8 H15); invert 1; linear_arithmetic.
  invert H15.
  invert H10.
Qed.

Theorem gratuitous_composition : forall t ch1 ch2 ch3,
    add2 ch1 ch2 || inTree_par t ch2 ch3
    <| addNs 2 ch1 ch2 || inTree_seq t ch2 ch3.
Proof.
  simplify.
  apply refines_Par.
  apply refines_add2.
  apply refines_inTree_par.
Qed.

Theorem gratuitous_composition_expanded : forall n t ch1 ch2 ch3,
    mem (n + 2) t = true
    -> (!!ch1(n); Done) || (add2 ch1 ch2 || inTree_par t ch2 ch3)
       <| (!!ch1(n); Done) || (!!ch2(n+2); Done) || (!!ch3(tt); Done).
Proof.
  simplify.
  eapply refines_trans.
  apply refines_Par.
  apply refines_refl.
  apply gratuitous_composition.
  unfold addNs, addN, inTree_seq.
Admitted.
