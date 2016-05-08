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
| BlockChannel (ch : channel) (pr : proc)
| Send (ch : channel) {A : Set} (v : A) (k : proc)
| Recv (ch : channel) {A : Set} (k : A -> proc)
| Par (pr1 pr2 : proc)
| Dup (pr : proc)
| Done.

Notation pid := nat (only parsing).
Notation procs := (fmap pid proc).
Notation channels := (set channel).

Notation "'New' ls ( x ) ; k" := (NewChannel ls (fun x => k)) (right associativity, at level 51, ls at level 0).
Notation "'Block' ch ; k" := (BlockChannel ch k) (right associativity, at level 51).
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

Definition notUse (ch : channel) (l : label) :=
  match l with
  | Action (Input r) => r.(Channel) <> ch
  | Action (Output r) => r.(Channel) <> ch
  | Silent => True
  end.

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
| LStepNew : forall chs ch k,
    ~In ch chs
    -> lstep (NewChannel chs k) Silent (BlockChannel ch (k ch))
| LStepBlock : forall ch k l k',
    lstep k l k'
    -> notUse ch l
    -> lstep (BlockChannel ch k) l (BlockChannel ch k')
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

Theorem refines_couldGenerate : forall pr1 pr2, pr1 <| pr2
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
Hint Unfold lstepSilent.

Ltac lists' :=
  repeat match goal with
         | [ H : NoDup _ |- _ ] => invert H
         | [ |- NoDup _ ] => constructor
         end; simplify; propositional; equality || linear_arithmetic.

Ltac lists := solve [ lists' ].

Hint Extern 1 (NoDup _) => lists.


(** * Examples *)

Definition add2_once (input output : channel) : proc :=
  New[input;output](intermediate);
  (addN 1 input intermediate
   || addN 1 intermediate output).

Inductive R_add2 : proc -> proc -> Prop :=
| Initial : forall input output,
    input <> output
    -> R_add2
         (New[input;output](ch); ??input(n : nat); !!ch(n + 1); Done
                              || ??ch(n : nat); !!output (n + 1); Done)
         (??input(n : nat); !!output(n + 2); Done)
| ChoseIntermediate : forall input output intermediate,
    NoDup [input; output; intermediate]
    -> R_add2
         (Block intermediate; ??input(n : nat); !!intermediate(n + 1); Done
                              || ??intermediate(n : nat); !!output (n + 1); Done)
         (??input(n : nat); !!output(n + 2); Done)
| GotInput : forall input output intermediate n,
    NoDup [input; output; intermediate]
    -> R_add2
         (Block intermediate; !!intermediate(n + 1); Done
                              || ??intermediate(n : nat); !!output (n + 1); Done)
         (!!output(n + 2); Done)
| HandedOff : forall input output intermediate n,
    NoDup [input; output; intermediate]
    -> R_add2
         (Block intermediate; Done || (!!output(n + 2); Done))
         (!!output(n + 2); Done)
| Finished : forall input output intermediate,
    NoDup [input; output; intermediate]
    -> R_add2
         (Block intermediate; Done || Done)
         Done.

Hint Constructors R_add2.

Theorem add2_once_refines_addN : forall input output,
    input <> output
    -> add2_once input output <| addN 2 input output.
Proof.
  simplify.
  exists R_add2.
  first_order.

  clear input output H.
  invert H0; simplify; inverter; eauto.
  replace (n + 1 + 1) with (n + 2) by linear_arithmetic.
  eauto.

  clear input output H.
  invert H0; simplify; inverter; eauto 10; simplify; equality.

  unfold add2_once, addN; eauto.
Qed.


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


(** ** Block *)

Inductive RBlock (R : proc -> proc -> Prop) : proc -> proc -> Prop :=
| RBlock1 : forall pr1 pr2 ch,
    R pr1 pr2
    -> RBlock R (Block ch; pr1) (Block ch; pr2).

Hint Constructors RBlock.
Hint Unfold notUse.

Lemma lstepSilent_Block : forall ch pr1 pr2,
    lstepSilent^* pr1 pr2
    -> lstepSilent^* (Block ch; pr1) (Block ch; pr2).
Proof.
  induct 1; eauto.
Qed.

Hint Resolve lstepSilent_Block.

Theorem refines_Block : forall pr1 pr2 ch,
    pr1 <| pr2
    -> Block ch; pr1 <| Block ch; pr2.
Proof.
  invert 1.
  exists (RBlock x).
  first_order; eauto.

  invert H2.
  invert H3.
  eapply H in H6; eauto.
  first_order.
  eauto.

  invert H2.
  invert H3.
  eapply H0 in H6; eauto.
  first_order.
  eauto 10.
Qed.

Inductive RBlock2 : proc -> proc -> Prop :=
| RBlock2_1 : forall ch1 ch2 pr,
    RBlock2 (Block ch1; Block ch2; pr) (Block ch2; Block ch1; pr).

Hint Constructors RBlock2.

Theorem refines_Block2 : forall ch1 ch2 pr,
    Block ch1; Block ch2; pr <| Block ch2; Block ch1; pr.
Proof.
  exists RBlock2.
  first_order; eauto.

  invert H.
  invert H0.
  invert H2.
  eauto 10.

  invert H.
  invert H0.
  invert H2.
  eauto 10.
Qed.

Inductive neverUses (ch : channel) : proc -> Prop :=
| NuRecv : forall ch' (A : Set) (k : A -> _),
    ch' <> ch
    -> (forall v, neverUses ch (k v))
    -> neverUses ch (Recv ch' k)
| NuSend : forall ch' (A : Set) (v : A) k,
    ch' <> ch
    -> neverUses ch k
    -> neverUses ch (Send ch' v k)
| NuDup : forall pr,
    neverUses ch pr
    -> neverUses ch (Dup pr)
| NuPar : forall pr1 pr2,
    neverUses ch pr1
    -> neverUses ch pr2
    -> neverUses ch (pr1 || pr2)
| NuDone :
    neverUses ch Done.

Hint Constructors neverUses.

Lemma neverUses_step : forall ch pr1,
    neverUses ch pr1
    -> forall l pr2, lstep pr1 l pr2
                     -> neverUses ch pr2.
Proof.
  induct 1; invert 1; eauto.
Qed.

Hint Resolve neverUses_step.

Inductive RBlockS : proc -> proc -> Prop :=
| RBlockS1 : forall ch pr1 pr2,
    neverUses ch pr2
    -> RBlockS (Block ch; pr1 || pr2) ((Block ch; pr1) || pr2).

Hint Constructors RBlockS.

Lemma neverUses_notUse : forall ch pr l,
    neverUses ch pr
    -> forall pr', lstep pr l pr'
                   -> notUse ch l.
Proof.
  induct 1; invert 1; simplify; eauto.
Qed.

Lemma notUse_Input_Output : forall ch r,
    notUse ch (Input r)
    -> notUse ch (Output r).
Proof.
  simplify; auto.
Qed.

Lemma notUse_Output_Input : forall ch r,
    notUse ch (Output r)
    -> notUse ch (Input r).
Proof.
  simplify; auto.
Qed.

Hint Resolve neverUses_notUse.

Theorem refines_BlockS : forall ch pr1 pr2,
    neverUses ch pr2
    -> Block ch; pr1 || pr2 <| (Block ch; pr1) || pr2.
Proof.
  exists RBlockS.
  first_order; eauto.

  invert H0.
  invert H1.
  invert H4; eauto 10.
  eexists; propositional.
  apply trc_one.
  eapply LStepRendezvousLeft; eauto.
  constructor; eauto.
  apply notUse_Output_Input; eauto.
  eauto.
  eexists; propositional.
  apply trc_one.
  eapply LStepRendezvousRight; eauto.
  constructor; eauto.
  apply notUse_Input_Output; eauto.
  eauto.

  invert H0.
  invert H1.
  invert H4; eauto 10.
Qed.


(** * Example again *)

Theorem refines_add2 : forall input output,
    input <> output
    -> add2 input output <| addNs 2 input output.
Proof.
  simplify.
  apply refines_Dup.
  apply add2_once_refines_addN; auto.
Qed.

Theorem refines_add2_with_tester : forall metaInput input output metaOutput,
    input <> output
    -> Block input; Block output; add2 input output || tester metaInput input output metaOutput
       <| Block input; Block output; addNs 2 input output || tester metaInput input output metaOutput.
Proof.
  simplify.
  do 2 apply refines_Block.
  apply refines_Par.
  apply refines_add2; auto.
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
| TreeGotInput : forall n,
    RTree t input output
          (New[input;output](output');
            inTree_par' n t output'
            || ??output'(_ : unit);
               !!output(tt);
               Done)
          (if mem n t then
             !!output(tt);
             Done
           else
             Done)
| TreeSearching : forall n output' threads,
    ~In output' [input; output]
    -> TreeThreads output' (mem n t) threads
    -> RTree t input output
          (Block output';
            threads
            || ??output'(_ : unit);
               !!output(tt);
               Done)
          (if mem n t then
             !!output(tt);
             Done
           else
             Done)
| TreeFound : forall n output' threads,
    mem n t = true
    -> ~In output' [input; output]
    -> TreeThreads output' true threads
    -> RTree t input output
             (Block output'; threads || !!output(tt); Done)
             (!!output(tt); Done)
| TreeNotified : forall n output' threads,
    mem n t = true
    -> ~In output' [input; output]
    -> TreeThreads output' true threads
    -> RTree t input output
          (Block output'; threads || Done)
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

Theorem refines_inTree_par : forall t input output,
    inTree_par t input output <| inTree_seq t input output.
Proof.
  simplify.
  apply refines_Dup.
  exists (RTree t input output).
  first_order; eauto.

  invert H.

  invert H0.
  invert H0; eauto.
  invert H0.
  invert H4; eauto.
  invert H6.
  eapply TreeThreads_actionIs in H3; eauto; equality.
  specialize (TreeThreads_actionIs H2 H3); invert 1.
  invert H5.
  assert (mem n t = true) by eauto.
  rewrite H.
  eauto 10.
  invert H0.
  invert H5.
  eauto.
  invert H7.
  eapply TreeThreads_actionIs in H4; eauto; equality.
  invert H6.
  invert H0.
  invert H5.
  exfalso; eauto using TreeThreads_silent.
  invert H7.
  invert H6.
  invert H6.

  invert H.

  invert H0; eauto.
  invert H0.
  invert H0.
  invert H4.
  eapply TreeThreads_actionIs in H6; eauto.
  subst; simplify; equality.
  invert H6.
  simplify; equality.
  invert H0.
  invert H5.
  eapply TreeThreads_actionIs in H7; eauto.
  subst; simplify; equality.
  invert H7.
  eauto 10.
  invert H0.
  invert H5.
  eapply TreeThreads_actionIs in H7; eauto.
  subst; simplify; equality.
  invert H7.
Qed.

Theorem gratuitous_composition : forall t ch1 ch2 ch3,
    ch1 <> ch2
    -> Block ch2; add2 ch1 ch2 || inTree_par t ch2 ch3
       <| Block ch2; addNs 2 ch1 ch2 || inTree_seq t ch2 ch3.
Proof.
  simplify.
  apply refines_Block.
  apply refines_Par.
  apply refines_add2; auto.
  apply refines_inTree_par.
Qed.


(** * One more example: handoff lemma *)

Inductive manyOf (this : proc) : proc -> Prop :=
| MoOne : manyOf this this
| MoDup : manyOf this (Dup this)
| MoPar : forall pr1 pr2,
    manyOf this pr1
    -> manyOf this pr2
    -> manyOf this (pr1 || pr2).

Inductive manyOfAndOneOf (common rare : proc) : proc -> Prop :=
| MooCommon : manyOfAndOneOf common rare common
| MooRare : manyOfAndOneOf common rare rare
| MooDup : manyOfAndOneOf common rare (Dup common)
| MooPar1 : forall pr1 pr2,
    manyOfAndOneOf common rare pr1
    -> manyOf common pr2
    -> manyOfAndOneOf common rare (pr1 || pr2)
| MooPar2 : forall pr1 pr2,
    manyOf common pr1
    -> manyOfAndOneOf common rare pr2
    -> manyOfAndOneOf common rare (pr1 || pr2).

Inductive Rhandoff (ch : channel) (A : Set) (v : A) (k : A -> proc) : proc -> proc -> Prop :=
| Rhandoff1 : forall recvs,
    neverUses ch (k v)
    -> manyOf (??ch(x : A); k x) recvs
    -> Rhandoff ch v k (Block ch; !!ch(v); Done || recvs) (k v)
| Rhandoff2 : forall recvs rest,
    neverUses ch rest
    -> manyOfAndOneOf (??ch(x : A); k x) rest recvs
    -> Rhandoff ch v k (Block ch; Done || recvs) rest
| Rhandoff3 : forall recvs rest,
    neverUses ch rest
    -> manyOf (??ch(x : A); k x) recvs
    -> Rhandoff ch v k (Block ch; Done || recvs) rest.

Hint Constructors manyOf manyOfAndOneOf Rhandoff.

Lemma manyOf_action : forall this pr,
    manyOf this pr
    -> forall a pr', lstep pr (Action a) pr'
                          -> exists this', lstep this a this'.
Proof.
  induct 1; simplify; eauto.
  invert H.
  invert H1; eauto.
Qed.

Lemma manyOf_silent : forall this, (forall this', lstepSilent this this' -> False)
    -> (forall r this', lstep this (Output r) this' -> False)
    -> forall pr, manyOf this pr
      -> forall pr', lstep pr Silent pr'
                     -> manyOf this pr'.
Proof.
  induct 1; simplify; eauto.
  exfalso; eauto.
  invert H1; eauto.
  invert H1; eauto.
  eapply manyOf_action in H5; eauto; first_order.
  eapply manyOf_action in H4; eauto; first_order.
Qed.

Lemma manyOf_rendezvous : forall ch (A : Set) (v : A) (k : A -> _) pr,
    manyOf (Recv ch k) pr
    -> forall pr', lstep pr (Input {| Channel := ch; Value := v |}) pr'
                   -> manyOfAndOneOf (Recv ch k) (k v) pr'.
Proof.
  induct 1; simplify; eauto.

  invert H; eauto.

  invert H.

  invert H1; eauto.
Qed.

Hint Resolve manyOf_silent manyOf_rendezvous.

Lemma manyOfAndOneOf_output : forall ch (A : Set) (k : A -> _) rest ch0 (A0 : Set) (v0 : A0) pr,
    manyOfAndOneOf (Recv ch k) rest pr
    -> forall pr', lstep pr (Output {| Channel := ch0; Value := v0 |}) pr'
                   -> exists rest', lstep rest (Output {| Channel := ch0; Value := v0 |}) rest'
                                    /\ manyOfAndOneOf (Recv ch k) rest' pr'.
Proof.
  induct 1; simplify; eauto.

  invert H.

  invert H.

  invert H1; eauto.
  apply IHmanyOfAndOneOf in H6; first_order; eauto.
  eapply manyOf_action in H0; eauto.
  first_order.
  invert H0.

  invert H1; eauto.
  eapply manyOf_action in H; eauto.
  first_order.
  invert H.
  apply IHmanyOfAndOneOf in H6; first_order; eauto.
Qed.

Lemma manyOf_manyOfAndOneOf : forall this other pr,
    manyOf this pr
    -> manyOfAndOneOf this other pr.
Proof.
  induct 1; simplify; eauto.
Qed.

Hint Resolve manyOf_manyOfAndOneOf.

Lemma no_rendezvous : forall ch0 (A0 : Set) (v : A0) pr1 rest (k : A0 -> _),
    manyOfAndOneOf (??ch0 (x : _); k x) rest pr1
    -> forall pr1', lstep pr1 (Output {| Channel := ch0; TypeOf := A0; Value := v |}) pr1'
    -> neverUses ch0 rest
    -> False.
Proof.
  induct 1; simplify.

  invert H.

  invert H.
  invert H0; equality.
  invert H0.
  invert H0.
  eapply neverUses_notUse in H3; eauto.
  simplify; equality.
  invert H0.
  eapply neverUses_notUse in H4; eauto.
  simplify; equality.

  invert H.

  invert H1.
  eauto.
  eapply manyOf_action in H0; try eassumption.
  first_order.
  invert H0.

  invert H1.
  eapply manyOf_action in H7; try eassumption.
  first_order.
  invert H1.
  eauto.
Qed.

Lemma manyOfAndOneOf_silent : forall ch (A : Set) (k : A -> _) rest pr,
    manyOfAndOneOf (Recv ch k) rest pr
    -> neverUses ch rest
    -> forall pr', lstep pr Silent pr'
                   -> exists rest', manyOfAndOneOf (Recv ch k) rest' pr'
                                    /\ (rest = rest' \/ lstep rest Silent rest').
Proof.
  induct 1; simplify; eauto.
  invert H0.
  invert H0; eauto.
  invert H2.
  apply IHmanyOfAndOneOf in H7; auto.
  first_order; eauto.
  eexists; propositional.
  apply MooPar1.
  eauto.
  eapply manyOf_silent; try eassumption; invert 1.
  eapply manyOf_action in H6; eauto.
  first_order.
  invert H2.
  eapply manyOf_action in H6; eauto.
  first_order.
  invert H2.
  exfalso; eapply no_rendezvous; eassumption.
  invert H2.
  eexists; propositional.
  apply MooPar2; auto.
  eapply manyOf_silent; try eassumption; invert 1.
  apply IHmanyOfAndOneOf in H7; first_order; eauto.
  eapply manyOf_action in H5; eauto.
  first_order.
  invert H2.
  exfalso; eapply no_rendezvous; eassumption.
  eapply manyOf_action in H; eauto.
  first_order.
  invert H.
Qed.

Hint Resolve manyOfAndOneOf_silent manyOf_rendezvous.

Lemma manyOfAndOneOf_action : forall ch (A : Set) (k : A -> _) rest pr,
    manyOfAndOneOf (Recv ch k) rest pr
    -> forall a pr', lstep pr (Action a) pr'
                     -> (exists v : A, a = Input {| Channel := ch; Value := v |})
                        \/ exists rest', manyOfAndOneOf (Recv ch k) rest' pr'
                                         /\ lstep rest a rest'.
Proof.
  induct 1; simplify; eauto.
  invert H; eauto.
  invert H.
  invert H1.
  apply IHmanyOfAndOneOf in H6; first_order; subst; eauto.
  eapply manyOf_action in H6; eauto.
  first_order.
  invert H1; eauto.
  invert H1.
  eapply manyOf_action in H6; eauto.
  first_order.
  invert H1; eauto.
  apply IHmanyOfAndOneOf in H6; first_order; subst; eauto.
Qed.

Theorem handoff : forall ch (A : Set) (v : A) k,
    neverUses ch (k v)
    -> Block ch; (!!ch(v); Done) || Dup (Recv ch k)
       <| k v.
Proof.
  simplify.
  exists (Rhandoff ch v k).
  first_order; eauto.

  invert H0.

  invert H1.
  invert H5.
  invert H7.
  eexists; propositional; eauto.
  apply Rhandoff1; auto.
  eapply manyOf_silent; try eassumption; invert 1.
  invert H4.
  invert H4; eauto.
  invert H1.
  invert H5.
  invert H7.
  eapply manyOfAndOneOf_silent in H7; eauto.
  first_order; subst; eauto.
  eauto 6.
  invert H4.
  invert H4.
  invert H1.
  invert H5.
  invert H7.
  exists pr2; propositional; eauto.
  apply Rhandoff3; auto.
  eapply manyOf_silent; try eassumption; invert 1.
  invert H4.
  invert H4.

  invert H0.

  invert H1.
  invert H5.
  invert H7.
  simplify; equality.
  eapply manyOf_action in H7; eauto.
  first_order.
  invert H0.
  simplify; equality.
  invert H1.
  invert H5.
  invert H7.
  eapply manyOfAndOneOf_action in H3; eauto.
  first_order; subst; eauto 10.
  simplify; equality.
  invert H1.
  invert H5.
  invert H7.
  eapply manyOf_action in H7; eauto.
  first_order.
  invert H0.
  simplify; equality.
Qed.

Ltac neverUses :=
  repeat match goal with
         | [ |- context[if ?E then _ else _] ] => cases E
         | _ => repeat (constructor; simplify)
         end; lists.
  
Theorem gratuitous_composition_expanded : forall n t ch1 ch2 ch3,
    mem (n + 2) t = true
    -> NoDup [ch1; ch2; ch3]
    -> Block ch1; Block ch2; !!ch1(n); Done || add2 ch1 ch2 || inTree_par t ch2 ch3
       <| !!ch3(tt); Done.
Proof.
  simplify.
  eapply refines_trans.
  do 2 eapply refines_Block.
  apply refines_Par.
  apply refines_Par.
  apply refines_refl.
  apply refines_add2; lists.
  apply refines_inTree_par.
  unfold addNs, addN, inTree_seq.
  eapply refines_trans.
  eapply refines_Block2.
  eapply refines_trans.
  eapply refines_Block.
  eapply refines_trans.
  apply refines_BlockS; neverUses.
  apply refines_Par.
  apply handoff; neverUses.
  apply refines_refl.
  eapply refines_trans.
  apply handoff; neverUses.
  rewrite H.
  apply refines_refl.
Qed.
