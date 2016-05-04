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
