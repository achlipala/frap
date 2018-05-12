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
| TPar (t1 t2 : type)
| TDup (t : type)
| TDone

| InternalChoice (t1 t2 : type)
| ExternalChoice (t1 t2 : type).

Infix "||" := Par : st_scope.
Delimit Scope st_scope with st.
Bind Scope st_scope with type.
Notation "!!! ch ( A ) ; k" := (TSend ch A k%st) (right associativity, at level 45, ch at level 0) : st_scope.
Notation "??? ch ( A ) ; k" := (TRecv ch A k%st) (right associativity, at level 45, ch at level 0) : st_scope.
Infix "|?|" := InternalChoice (at level 40) : st_scope.
Infix "?|?" := ExternalChoice (at level 40) : st_scope.


Inductive ignoresChannel (ch : channel) : type -> Prop :=
| IcSend : forall ch' A t,
    ch' <> ch
    -> ignoresChannel ch t
    -> ignoresChannel ch (TSend ch' A t)
| IcRecv : forall ch' A t,
    ch' <> ch
    -> ignoresChannel ch t
    -> ignoresChannel ch (TRecv ch' A t)
| IcPar : forall t1 t2,
    ignoresChannel ch t1
    -> ignoresChannel ch t2
    -> ignoresChannel ch (TPar t1 t2)
| IcDup : forall t,
    ignoresChannel ch t
    -> ignoresChannel ch (TDup t)
| IcDone :
    ignoresChannel ch TDone

| IcInternalChoice : forall t1 t2,
    ignoresChannel ch t1
    -> ignoresChannel ch t2
    -> ignoresChannel ch (InternalChoice t1 t2)
| IcExternalChoice : forall t1 t2,
    ignoresChannel ch t1
    -> ignoresChannel ch t2
    -> ignoresChannel ch (ExternalChoice t1 t2).

Inductive hideChannel (ch : channel) : type -> type -> Prop :=
| HideIgnored : forall t,
    ignoresChannel ch t
    -> hideChannel ch t t

| HideExtSend1 : forall ch' A t1 t2 t',
    ch' <> ch
    -> ignoresChannel ch' t2
    -> hideChannel ch (TPar t1 t2) t'
    -> hideChannel ch (TPar (TSend ch' A t1) t2) (TSend ch' A t')
| HideExtRecv1 : forall ch' A t1 t2 t',
    ch' <> ch
    -> ignoresChannel ch' t2
    -> hideChannel ch (TPar t1 t2) t'
    -> hideChannel ch (TPar (TRecv ch' A t1) t2) (TRecv ch' A t')
| HideExtSend2 : forall ch' A t1 t2 t',
    ch' <> ch
    -> ignoresChannel ch' t2
    -> hideChannel ch (TPar t1 t2) t'
    -> hideChannel ch (TPar t1 (TSend ch' A t2)) (TSend ch' A t')
| HideExtRecv2 : forall ch' A t1 t2 t',
    ch' <> ch
    -> ignoresChannel ch' t2
    -> hideChannel ch (TPar t1 t2) t'
    -> hideChannel ch (TPar t1 (TRecv ch' A t2)) (TRecv ch' A t')

| HideRendezvous1 : forall A t1 t2 t',
    hideChannel ch (TPar t1 t2) t'
    -> hideChannel ch (TPar (TSend ch A t1) (TRecv ch A t2)) t'
| HideRendezvous2 : forall A t1 t2 t',
    hideChannel ch (TPar t1 t2) t'
    -> hideChannel ch (TPar (TRecv ch A t1) (TSend ch A t2)) t'.

Fixpoint shrink (t : type) : type :=
  match t with
  | TSend ch A t1 => TSend ch A (shrink t1)
  | TRecv ch A t1 => TRecv ch A (shrink t1)
  | TPar t1 t2 =>
    let t1' := shrink t1 in
    let t2' := shrink t2 in
    match t1', t2' with
    | TDone, _ => t2'
    | _, TDone => t1'
    | _, _ => TPar t1' t2'
    end
  | TDup t1 =>
    let t1' := shrink t1 in
    match t1' with
    | TDone => TDone
    | _ => TDup t1'
    end
  | TDone => TDone

  | InternalChoice t1 t2 => InternalChoice (shrink t1) (shrink t2)
  | ExternalChoice t1 t2 => ExternalChoice (shrink t1) (shrink t2)
  end.

Inductive hasty : proc -> type -> Prop :=
| HtNewChannel : forall notThese k t tc tcs,
    (forall ch, ~In ch notThese -> hasty (k ch) (t ch))
    -> (forall ch, ~In ch notThese -> hideChannel ch (t ch) tc)
    -> shrink tc = tcs
    -> hasty (NewChannel notThese k) tcs
| HtBlockChannel : forall ch pr t tc tcs,
    hasty pr t
    -> hideChannel ch t tc
    -> shrink tc = tcs
    -> hasty (BlockChannel ch pr) tcs
| HtSend : forall ch (A : Set) (v : A) k t,
    hasty k t
    -> hasty (Send ch v k) (TSend ch A t)
| HtRecv : forall ch (A : Set) (k : A -> _) t,
    (forall v, hasty (k v) t)
    -> hasty (Recv ch k) (TRecv ch A t)
| HtPar : forall pr1 pr2 t1 t2,
    hasty pr1 t1
    -> hasty pr2 t2
    -> hasty (Par pr1 pr2) (TPar t1 t2)
| HtDup : forall pr t,
    hasty pr t
    -> hasty (Dup pr) (TDup t)
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

Theorem addN_typed : forall k input output,
    hasty (addN k input output) (???input(nat); !!!output(nat); TDone).
Proof.
  simplify.
  repeat (constructor; simplify).
Qed.

Definition add2 (input output : channel) : proc :=
  Dup (New[input;output](intermediate);
        addN 1 input intermediate
        || addN 1 intermediate output).

Ltac hide1 := apply HideRendezvous1 || apply HideRendezvous2
              || (eapply HideIgnored; repeat constructor; equality)
              || (eapply HideExtSend1; [ equality | repeat constructor; equality | ])
              || (eapply HideExtRecv1; [ equality | repeat constructor; equality | ])
              || (eapply HideExtSend2; [ equality | repeat constructor; equality | ])
              || (eapply HideExtRecv2; [ equality | repeat constructor; equality | ]).

Ltac hide := repeat hide1.

Ltac hasty1 :=
  match goal with
  | [ |- hasty _ _ ] => econstructor; simplify
  end.

Ltac hasty := simplify; repeat hasty1; simplify; hide; try equality.

Theorem add2_typed : forall input output,
    input <> output
    -> hasty (add2 input output) (TDup (???input(nat); !!!output(nat); TDone)).
Proof.
  hasty.
Qed.


(** * Complementing Types *)

Fixpoint complement (t : type) : type :=
  match t with
  | TSend ch A t1 => TRecv ch A (complement t1)
  | TRecv ch A t1 => TSend ch A (complement t1)
  | TPar t1 t2 => TPar (complement t1) (complement t2)
  | TDup t1 => TDup (complement t1)
  | TDone => TDone

  | InternalChoice t1 t2 => ExternalChoice (complement t1) (complement t2)
  | ExternalChoice t1 t2 => InternalChoice (complement t1) (complement t2)
  end.

Definition add2_client (input output : channel) : proc :=
  Dup (!!input(42);
       ??output(_ : nat);
       Done).

Theorem add2_client_typed : forall input output,
    input <> output
    -> hasty (add2_client input output) (complement (TDup (???input(nat); !!!output(nat); TDone))).
Proof.
  hasty.
Qed.
