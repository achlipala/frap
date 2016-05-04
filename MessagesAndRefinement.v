(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 15: Pi-Calculus and Behavioral Refinement
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.
Set Asymmetric Patterns.


Notation channel := nat.

Inductive proc :=
| NewChannel (k : channel -> proc)
| Send (ch : channel) {A : Set} (v : A) (k : proc)
| Recv (ch : channel) {A : Set} (k : A -> proc)
| Par (pr1 pr2 : proc)
| Dup (pr : proc).

Notation pid := nat.
Notation procs := (fmap pid proc).
Notation channels := (set channel).

Inductive step : channels * procs -> channels * procs -> Prop :=
| StepNew : forall chs ps i k ch,
    ps $? i = Some (NewChannel k)
    -> ~ch \in chs
    -> step (chs, ps) (chs \cup {ch}, ps $+ (i, k ch))
| StepSendRecv : forall chs ps i ch {A : Set} (v : A) k1 j k2,
    ps $? i = Some (Send ch v k1)
    -> ps $? j = Some (Recv ch k2)
    -> step (chs, ps) (chs, ps $+ (i, k1) $+ (j, k2 v))
| StepPar : forall chs ps i pr1 pr2 j,
    ps $? i = Some (Par pr1 pr2)
    -> ps $? j = None
    -> step (chs, ps) (chs, ps $+ (i, pr1) $+ (j, pr2))
| StepDup : forall chs ps i pr j,
    ps $? i = Some (Dup pr)
    -> ps $? j = None
    -> step (chs, ps) (chs, ps $+ (i, Dup pr) $+ (j, pr)).


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
| LStepNew : forall k l k',
    (forall ch, lstep (k ch) l (k' ch))
    -> lstep (NewChannel k) l (NewChannel k')
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

Definition refines (pr1 pr2 : proc) :=
  forall tr, couldGenerate pr1 tr -> couldGenerate pr2 tr.
