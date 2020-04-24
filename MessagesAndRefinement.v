(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 19: Process Algebra and Behavioral Refinement
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap Eqdep FunctionalExtensionality.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * First, an unexplained tactic that will come in handy.... *)

Ltac invert H := (FrapWithoutSets.invert H || (inversion H; clear H));
                 repeat match goal with
                        | [ x : _ |- _ ] => subst x
                        | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; try subst
                        end.


(** * A process algebra: syntax and semantics *)

(* A process algebra defines a set of communicating *processes*, which might
 * more commonly be called *threads*.  Typically processes communicate not with
 * locks and shared memory, as they have in the prior two chapters, but instead
 * with *message passing*.  Messages are passed over synchronous *channels*,
 * which we will just represent as numbers. *)
Notation channel := nat (only parsing).

(* Here are the basic syntactic constructions of processes. *)
Inductive proc :=
| NewChannel (notThese : list channel) (k : channel -> proc)
(* Pick a new channel name [ch] not found in [notThese], and continue like
 * [k ch]. *)

| BlockChannel (ch : channel) (pr : proc)
(* Act like [pr], but prevent interaction with other processes through channel
 * [ch].  We effectively force [ch] to be *private*. *)

| Send (ch : channel) {A : Type} (v : A) (k : proc)
| Recv (ch : channel) {A : Type} (k : A -> proc)
(* When one process runs a [Send] and the other a [Recv] on the same channel
 * simultaneously, the [Send] moves on to its [k], while the [Recv] moves on to
 * its [k v], for [v] the value that was sent. *)

| Par (pr1 pr2 : proc)
(* This one, at least, is just like it was in the last chapter: parallel
 * composition of threads. *)

| Dup (pr : proc)
(* An idiosyncratic convention of process algebra: [Dup pr] acts like an
 * *infinite* number of *copies* of [pr].  It replaces conventional loops. *)

| Done
(* This process can't do anything *).

(* Some nicer notations: *)
Notation "'New' ls ( x ) ; k" := (NewChannel ls (fun x => k)) (right associativity, at level 51, ls at level 0).
Notation "'Block' ch ; k" := (BlockChannel ch k) (right associativity, at level 51).
Notation "!! ch ( v ) ; k" := (Send ch v k) (right associativity, at level 45, ch at level 0).
Notation "?? ch ( x : T ) ; k" := (Recv ch (fun x : T => k)) (right associativity, at level 45, ch at level 0, x at level 0).
Infix "||" := Par.


(** * Example *)

(* Let's build highly exciting processes for adding constants to numbers. *)

(* This one accepts one number [n] on channel [input] and returns [n + k] as the
 * result, by writing it to [output]. *)
Definition addN (k : nat) (input output : channel) : proc :=
  ??input(n : nat);
  !!output(n + k);
  Done.

(* We wrap that last one in a [Dup] to turn it into a kind of immortal server,
 * happy to keep responding to "please add k to this" requests forever. *)
Definition addNs (k : nat) (input output : channel) : proc :=
  Dup (addN k input output).

(* Chaining together two "+1" boxes is one way to build an alternative "+2"
 * box! *)
Definition add2 (input output : channel) : proc :=
  Dup (New[input;output](intermediate);
        addN 1 input intermediate
        || addN 1 intermediate output).

(* However we implement addition, we might compose with this tester process,
 * which uses an adder as a subroutine in a larger protocol.  [metaInput] and
 * [metaOutput] are the input and output of the whole system, while [input] and
 * [output] are used internally, say to communicate with an adder. *)
Definition tester (metaInput input output metaOutput : channel) : proc :=
  ??metaInput(n : nat);
  !!input(n * 2);
  ??output(r : nat);
  !!metaOutput(r);
  Done.


(** * Labeled semantics *)

(* Let's explain how programs run.  We'll give a flavor of operational semantics
 * called a "labeled transition system," because each step will include a label
 * that explains what happened.  In this case, the only relevant happenings are
 * sends or receives on channels.  Crucially, we suppress send/receive labels
 * for operations blocked by [Block]s. *)

Record message := {
  Channel : channel;
  TypeOf : Type;
  Value : TypeOf
}.

Inductive action :=
| Output (m : message)
| Input (m : message).

Inductive label :=
| Silent
| Action (a : action).

(* This predicate captures when a label doesn't use a channel. *)
Definition notUse (ch : channel) (l : label) :=
  match l with
  | Action (Input r) => r.(Channel) <> ch
  | Action (Output r) => r.(Channel) <> ch
  | Silent => True
  end.

(* Now, our labeled transition system: *)
Inductive lstep : proc -> label -> proc -> Prop :=

(* Sends and receives generate the expected labels.  Note that, for a [Recv],
 * the value being received is "pulled out of thin air"!  However, it gets
 * determined concretely by comparing against a matching [Send], in a rule that
 * we get to shortly. *)
| LStepSend : forall ch {A : Type} (v : A) k,
    lstep (Send ch v k)
          (Action (Output {| Channel := ch; Value := v |}))
          k
| LStepRecv : forall ch {A : Type} (k : A -> _) v,
    lstep (Recv ch k)
          (Action (Input {| Channel := ch; Value := v |}))
          (k v)

(* A [Dup] always has the option of replicating itself further. *)
| LStepDup : forall pr,
    lstep (Dup pr) Silent (Par (Dup pr) pr)

(* A channel allocation operation nondeterministically picks the new channel ID,
 * only checking that it isn't in the provided blacklist.  We install a [Block]
 * node to keep this channel truly private. *)
| LStepNew : forall chs ch k,
    ~In ch chs
    -> lstep (NewChannel chs k) Silent (BlockChannel ch (k ch))

(* [Block] nodes work as expected, disallowing labels that use the channel. *)
| LStepBlock : forall ch k l k',
    lstep k l k'
    -> notUse ch l
    -> lstep (BlockChannel ch k) l (BlockChannel ch k')

(* When either side of a parallel composition can step, we may bubble that step
 * up to the top. *)
| LStepPar1 : forall pr1 pr2 l pr1',
    lstep pr1 l pr1'
    -> lstep (Par pr1 pr2) l (Par pr1' pr2)
| LStepPar2 : forall pr1 pr2 l pr2',
    lstep pr2 l pr2'
    -> lstep (Par pr1 pr2) l (Par pr1 pr2')

(* These two symmetrical rules are the heart of how communication happens in our
 * language.  Namely, in a parallel composition, when one side is prepared to
 * write a value to a channel, and the other side is prepared to read the same
 * value from the same channel, the two sides *rendezvous*, and the value is
 * exchanged.  This is the only mechanism to let two transitions happen at
 * once. *)
| LStepRendezvousLeft : forall pr1 ch {A : Type} (v : A) pr1' pr2 pr2',
    lstep pr1 (Action (Input {| Channel := ch; Value := v |})) pr1'
    -> lstep pr2 (Action (Output {| Channel := ch; Value := v |})) pr2'
    -> lstep (Par pr1 pr2) Silent (Par pr1' pr2')
| LStepRendezvousRight : forall pr1 ch {A : Type} (v : A) pr1' pr2 pr2',
    lstep pr1 (Action (Output {| Channel := ch; Value := v |})) pr1'
    -> lstep pr2 (Action (Input {| Channel := ch; Value := v |})) pr2'
    -> lstep (Par pr1 pr2) Silent (Par pr1' pr2').

(* Here's a shorthand for silent steps. *)
Definition lstepSilent (pr1 pr2 : proc) := lstep pr1 Silent pr2.

(* Our key proof task will be to prove that one process "acts like" another.
 * We'll use *simulation* as the precise notion of "acts like." *)

(* We say that a relation [R] is a *simulation* when it satisfies the first two
 * conditions below.  The [simulates] predicate additionally asserts that a
 * particular pair of processes belongs to [R]. *)
Definition simulates (R : proc -> proc -> Prop) (pr1 pr2 : proc) :=
  (* First, consider a pair of processes related by [R].  When the lefthand
   * process can take a silent step, the righthand process can take zero or more
   * silent steps to "catch up," arriving at a new righthand process related to
   * the new lefthand process. *)
  (forall pr1 pr2, R pr1 pr2
                   -> forall pr1', lstepSilent pr1 pr1'
                                   -> exists pr2', lstepSilent^* pr2 pr2'
                                                   /\ R pr1' pr2')

  (* Now consider the same scenario where the lefthand process make a nonsilent
   * step.  We require that the righthand process can "catch up" in a way that
   * generates the same label that the lefthand process generated. *)
  /\ (forall pr1 pr2, R pr1 pr2
                      -> forall a pr1', lstep pr1 (Action a) pr1'
                                        -> exists pr2' pr2'', lstepSilent^* pr2 pr2'
                                                              /\ lstep pr2' (Action a) pr2''
                                                              /\ R pr1' pr2'')

  (* Finally, the provided process pair is in the relation. *)
  /\ R pr1 pr2.

(* One process *refines* another when there exists some simulation. *)
Definition refines (pr1 pr2 : proc) :=
  exists R, simulates R pr1 pr2.

Infix "<|" := refines (no associativity, at level 70).

(* That's a somewhat fancy notion of compatibility!  We can also relate it to
 * more intuitive conditions that aren't strong enough for many of the proofs we
 * want to do later. *)

(* This predicate captures all finite traces of actions that a process could
 * generate. *)
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

(* Skip ahead to [refines_couldGenerate] to see the top-level connection from
 * [refines]. *)

Hint Constructors couldGenerate : core.

Lemma lstepSilent_couldGenerate : forall pr1 pr2,
  lstepSilent^* pr1 pr2
  -> forall tr, couldGenerate pr2 tr
                -> couldGenerate pr1 tr.
Proof.
  induct 1; eauto.
Qed.

Hint Resolve lstepSilent_couldGenerate : core.

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

(* This theorem says that refinement implies *trace inclusion*. *)
Theorem refines_couldGenerate : forall pr1 pr2, pr1 <| pr2
    -> forall tr, couldGenerate pr1 tr
                  -> couldGenerate pr2 tr.
Proof.
  unfold refines; first_order; eauto using simulates_couldGenerate'.
Qed.


(** * Tactics for automating refinement proofs *)

(* Well, you're used to unexplained automation tactics by now, so here are some
 * more. ;-) *)

Lemma invert_Recv : forall ch (A : Type) (k : A -> proc) (x : A) pr,
    lstep (Recv ch k) (Action (Input {| Channel := ch; Value := x |})) pr
    -> pr = k x.
Proof.
  invert 1; auto.
Qed.

Ltac inverter :=
  repeat match goal with
         | [ H : lstep _ _ _ |- _ ] => (apply invert_Recv in H; try subst) || invert H
         | [ H : lstepSilent _ _ |- _ ] => invert H
         end.

Hint Constructors lstep : core.
Hint Unfold lstepSilent : core.

Ltac lists' :=
  repeat match goal with
         | [ H : NoDup _ |- _ ] => invert H
         | [ |- NoDup _ ] => constructor
         end; simplify; propositional; equality || linear_arithmetic.

Ltac lists := solve [ lists' ].

Hint Extern 1 (NoDup _) => lists : core.


(** * Examples *)

(* OK, let's verify a simplification of the example we started with. *)
Definition add2_once (input output : channel) : proc :=
  New[input;output](intermediate);
  (addN 1 input intermediate
   || addN 1 intermediate output).

(* Here's our first, painstakingly crafted simulation relation.  It needs to
 * identify all pairs of processes that should be considered compatible.  Think
 * of the first process as the fancy *implementation* and the second process as
 * the simpler *specification*. *)
Inductive R_add2 : proc -> proc -> Prop :=
| Starting : forall input output,
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

Hint Constructors R_add2 : core.

Theorem add2_once_refines_addN : forall input output,
    input <> output
    -> add2_once input output <| addN 2 input output.
Proof.
  simplify.
  exists R_add2.
  first_order.

  invert H0; simplify; inverter; eauto.
  replace (n + 1 + 1) with (n + 2) by linear_arithmetic.
  eauto.

  invert H0; simplify; inverter; eauto 10; simplify; equality.

  unfold add2_once, addN; eauto.
Qed.

(* Well, good!  The fancy version doesn't produce any traces that the simple
 * version couldn't also produce.  (It may, however, fail to produce some traces
 * that the spec allows.) *)


(** * Compositional reasoning principles *)

(* It turns out that refinement has all sorts of convenient algebraic
 * properties.  To start with, it's a preorder. *)

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

  match goal with
  | [ H : _, H' : x _ _ |- _ ] => eapply H in H'; eauto; []
  end.
  first_order.
  eapply refines_trans' with (R := x0) in H7; eauto.
  first_order.

  match goal with
  | [ H : _, H' : x _ _ |- _ ] => eapply H in H'; eauto; []
  end.
  first_order.
  eapply refines_trans' with (R := x0) in H7; eauto.
  first_order.
  match goal with
  | [ H : _, H' : x0 _ _ |- _ ] => eapply H in H'; eauto; []
  end.
  first_order.
  eauto 8 using trc_trans.
Qed.


(** ** Dup *)

(* Refinement can be "pushed inside" a [Dup] operation. *)

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

Hint Constructors RDup : core.

Hint Unfold lstepSilent : core.

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

Hint Resolve lstepSilent_Par1 lstepSilent_Par2 : core.

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
  match goal with
  | [ _ : lstepSilent^* pr1' ?x |- _ ] => apply trc_trans with (x || pr2')
  end.
  eauto.
  match goal with
  | [ _ : lstepSilent^* pr2' ?x' |- lstepSilent^* (?x || _) _ ] => eapply trc_trans with (x || x')
  end.
  eauto.
  apply trc_one.
  eauto.
  eauto.
  eapply refines_Dup_Action in H4; eauto.
  eapply refines_Dup_Action in H5; eauto.
  first_order.
  eexists; propositional.
  match goal with
  | [ _ : lstepSilent^* pr1' ?x |- _ ] => apply trc_trans with (x || pr2')
  end.
  eauto.
  match goal with
  | [ _ : lstepSilent^* pr2' ?x' |- lstepSilent^* (?x || _) _ ] => eapply trc_trans with (x || x')
  end.
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

(* Refinement can also be "pushed inside" parallel composition. *)

Inductive RPar (R1 R2 : proc -> proc -> Prop) : proc -> proc -> Prop :=
| RPar1 : forall pr1 pr2 pr1' pr2',
    R1 pr1 pr1'
    -> R2 pr2 pr2'
    -> RPar R1 R2 (pr1 || pr2) (pr1' || pr2').

Hint Constructors RPar : core.

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
  match goal with
  | [ _ : lstepSilent^* pr1' ?x |- _ ] => apply trc_trans with (x || pr2')
  end.
  eauto.
  match goal with
  | [ _ : lstepSilent^* pr2' ?x' |- lstepSilent^* (?x || _) _ ] => eapply trc_trans with (x || x')
  end.
  eauto.
  apply trc_one.
  eauto.
  eauto.
  eapply H0 in H8; eauto.
  eapply H2 in H9; eauto.
  first_order.
  eexists; propositional.
  match goal with
  | [ _ : lstepSilent^* pr1' ?x |- _ ] => apply trc_trans with (x || pr2')
  end.
  eauto.
  match goal with
  | [ _ : lstepSilent^* pr2' ?x' |- lstepSilent^* (?x || _) _ ] => eapply trc_trans with (x || x')
  end.
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

(* A few similar properties apply to [Block], too. *)

Inductive RBlock (R : proc -> proc -> Prop) : proc -> proc -> Prop :=
| RBlock1 : forall pr1 pr2 ch,
    R pr1 pr2
    -> RBlock R (Block ch; pr1) (Block ch; pr2).

Hint Constructors RBlock : core.
Hint Unfold notUse : core.

Lemma lstepSilent_Block : forall ch pr1 pr2,
    lstepSilent^* pr1 pr2
    -> lstepSilent^* (Block ch; pr1) (Block ch; pr2).
Proof.
  induct 1; eauto.
Qed.

Hint Resolve lstepSilent_Block : core.

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

Hint Constructors RBlock2 : core.

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

(* This predicate is handy for side conditions, to enforce that a process never
 * uses a particular channel for anything. *)
Inductive neverUses (ch : channel) : proc -> Prop :=
| NuRecv : forall ch' (A : Type) (k : A -> _),
    ch' <> ch
    -> (forall v, neverUses ch (k v))
    -> neverUses ch (Recv ch' k)
| NuSend : forall ch' (A : Type) (v : A) k,
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

Hint Constructors neverUses : core.

Lemma neverUses_step : forall ch pr1,
    neverUses ch pr1
    -> forall l pr2, lstep pr1 l pr2
                     -> neverUses ch pr2.
Proof.
  induct 1; invert 1; eauto.
Qed.

Hint Resolve neverUses_step : core.

Inductive RBlockS : proc -> proc -> Prop :=
| RBlockS1 : forall ch pr1 pr2,
    neverUses ch pr2
    -> RBlockS (Block ch; pr1 || pr2) ((Block ch; pr1) || pr2).

Hint Constructors RBlockS : core.

Lemma neverUses_notUse : forall ch pr l,
    neverUses ch pr
    -> forall pr', lstep pr l pr'
                   -> notUse ch l.
Proof.
  induct 1; invert 1; simplify; eauto.
Qed.

Lemma notUse_Input_Output : forall ch r,
    notUse ch (Action (Input r))
    -> notUse ch (Action (Output r)).
Proof.
  simplify; auto.
Qed.

Lemma notUse_Output_Input : forall ch r,
    notUse ch (Action (Output r))
    -> notUse ch (Action (Input r)).
Proof.
  simplify; auto.
Qed.

Hint Resolve neverUses_notUse : core.

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


(** * The first example again *)

(* Those tools will help us lift our earlier adder proof to the immortal-server
 * case, without writing any new simulation relations ourselves. *)

Theorem refines_add2 : forall input output,
    input <> output
    -> add2 input output <| addNs 2 input output.
Proof.
  simplify.
  apply refines_Dup.
  apply add2_once_refines_addN; auto.
Qed.

(* We can even check refinement of our different adders when run together with
 * the tester, carefully marking internal channels as private with [Block]. *)
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

(* Here's one more example of a parallel program, which searches a binary tree
 * in parallel, checking if a value is found at one of the leaves. *)

Inductive tree :=
| Leaf (n : nat)
| Node (l r : tree).

(* This function formalizes the membership property that we check. *)
Fixpoint mem (n : nat) (t : tree) : bool :=
  match t with
  | Leaf m => if m ==n n then true else false
  | Node l r => mem n l || mem n r
  end%bool.

(* Here's the lame (but straightforward) sequential implementation.  Note that
 * we do nothing if the value is not found, and we send exactly one [tt] value
 * as output if the value is found. *)
Definition inTree_seq (t : tree) (input output : channel) :=
  Dup (??input(n : nat);
       if mem n t then
         !!output(tt);
         Done
       else
         Done).

(* Helper function for a fancier parallel version, creating many threads that
 * are all allowed to send to a channel [output], if they find the value. *)
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

(* Top-level wrapper for an immortal-server tree-searcher *)
Definition inTree_par (t : tree) (input output : channel) :=
  Dup (??input(n : nat);
       New[input;output](output');
       inTree_par' n t output'
       || ??output'(_ : unit);
          !!output(tt);
          Done).
(* Note the second part of the parallel composition, which makes sure we send
 * *at most one* notification to the outside world, though the internal threads
 * may generate as many notifications as there are tree leaves. *)

(* OK, now we get into the complex part, to prove the simulation.  We will let
 * the relations and lemmas below "speak for themselves," though admittedly it's
 * a pretty involved argument. *)

Inductive TreeThreads (output' : channel) : bool -> proc -> Prop :=
| TtDone : forall maySend,
    TreeThreads output' maySend Done
| TtSend :
    TreeThreads output' true (!!output'(tt); Done)
| TtPar : forall maySend pr1 pr2,
    TreeThreads output' maySend pr1
    -> TreeThreads output' maySend pr2
    -> TreeThreads output' maySend (pr1 || pr2).

(* This is the main simulation relation. *)
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

Hint Constructors TreeThreads RTree : core.

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

Hint Resolve TreeThreads_silent TreeThreads_maySend TreeThreads_action TreeThreads_weaken : core.

Lemma TreeThreads_inTree_par' : forall n ch t,
    TreeThreads ch (mem n t) (inTree_par' n t ch).
Proof.
  induct t; simplify; eauto.
  cases (n0 ==n n); eauto.
  cases (mem n t1); simplify; eauto.
  cases (mem n t2); simplify; eauto.
Qed.

Hint Resolve TreeThreads_inTree_par' : core.

(* Finally, the main theorem: *)
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

(* Hey, let's reason about plugging together the adder and the tree-searcher,
 * because we can!  The adder produces a number that is fed into the
 * tree-searcher as input. *)
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
(* Note how we didn't need to revisit any details of the proofs of the
 * individual components.  Now that's modularity in action! *)


(** * One more example: handoff lemma *)

(* Let's prove an even simpler specification related to the last example proof.
 * We define some relations and lemmas in service of the key handoff lemma, but
 * feel free to search for [Theorem] to skip ahead to its (much simpler)
 * statement. *)

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

Inductive Rhandoff (ch : channel) (A : Type) (v : A) (k : A -> proc) : proc -> proc -> Prop :=
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

Hint Constructors manyOf manyOfAndOneOf Rhandoff : core.

Lemma manyOf_action : forall this pr,
    manyOf this pr
    -> forall a pr', lstep pr (Action a) pr'
                          -> exists this', lstep this (Action a) this'.
Proof.
  induct 1; simplify; eauto.
  invert H.
  invert H1; eauto.
Qed.

Lemma manyOf_silent : forall this, (forall this', lstepSilent this this' -> False)
    -> (forall r this', lstep this (Action (Output r)) this' -> False)
    -> forall pr, manyOf this pr
      -> forall pr', lstep pr Silent pr'
                     -> manyOf this pr'.
Proof.
  induct 1; simplify; eauto.
  exfalso; eauto.
  invert H1; eauto.
  invert H1; eauto.
  eapply manyOf_action in H5; eauto; first_order; exfalso; eauto.
  eapply manyOf_action in H4; eauto; first_order; exfalso; eauto.
Qed.

Lemma manyOf_rendezvous : forall ch (A : Type) (v : A) (k : A -> _) pr,
    manyOf (Recv ch k) pr
    -> forall pr', lstep pr (Action (Input {| Channel := ch; Value := v |})) pr'
                   -> manyOfAndOneOf (Recv ch k) (k v) pr'.
Proof.
  induct 1; simplify; eauto.

  invert H; eauto.

  invert H.

  invert H1; eauto.
Qed.

Hint Resolve manyOf_silent manyOf_rendezvous : core.

Lemma manyOfAndOneOf_output : forall ch (A : Type) (k : A -> _) rest ch0 (A0 : Type) (v0 : A0) pr,
    manyOfAndOneOf (Recv ch k) rest pr
    -> forall pr', lstep pr (Action (Output {| Channel := ch0; Value := v0 |})) pr'
                   -> exists rest', lstep rest (Action (Output {| Channel := ch0; Value := v0 |})) rest'
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

Hint Resolve manyOf_manyOfAndOneOf : core.

Lemma no_rendezvous : forall ch0 (A0 : Type) (v : A0) pr1 rest (k : A0 -> _),
    manyOfAndOneOf (??ch0 (x : _); k x) rest pr1
    -> forall pr1', lstep pr1 (Action (Output {| Channel := ch0; TypeOf := A0; Value := v |})) pr1'
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

Lemma manyOfAndOneOf_silent : forall ch (A : Type) (k : A -> _) rest pr,
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

Hint Resolve manyOfAndOneOf_silent manyOf_rendezvous : core.

Lemma manyOfAndOneOf_action : forall ch (A : Type) (k : A -> _) rest pr,
    manyOfAndOneOf (Recv ch k) rest pr
    -> forall a pr', lstep pr (Action a) pr'
                     -> (exists v : A, a = Input {| Channel := ch; Value := v |})
                        \/ exists rest', manyOfAndOneOf (Recv ch k) rest' pr'
                                         /\ lstep rest (Action a) rest'.
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

(* When one thread is ready to send a message, and there is an immortal server
 * ready to accept that message, the process is equivalent to one that just
 * skips right to running a single server thread.  It is crucial that the body
 * of each server thread has nothing more to do with the channel we are using to
 * send it requests!  Otherwise, we would need to keep some [Dup] present
 * explicitly in the spec (righthand argument of [<|]). *)
Theorem handoff : forall ch (A : Type) (v : A) k,
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

(* OK, let's prove a final and satisfyingly simple spec for a system that
 * combines an adder and a tree-searcher.  We send some seed value to an adder,
 * which forwards it to the tree-searcher.  When the value we expect it to send
 * is indeed present in the tree, the whole contraption is equivalent to just
 * signalling a "yes" answer!  In our setting, that means sending a message to
 * the final output channel [ch3]. *)
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
(* Note how, again, we used the correctness theorems for our components as black
 * boxes, so that all that's left is algebraic reasoning over [<|]. *)
