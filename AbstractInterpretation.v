(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 7: Abstract Interpretation and Dataflow Analysis
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap Imp.

Set Implicit Arguments.


Record absint := {
  Typeof :> Set;
  (* This [:>] notation lets us treat any [absint] as its [Typeof],
   * automatically. *)
  Top : Typeof;
  (* The least precise element of the lattice *)
  Join : Typeof -> Typeof -> Typeof;
  (* Least upper bound of two elements *)
  Represents : nat -> Typeof -> Prop
  (* Which lattice elements represent which numbers? *)
}.

Definition absint_sound (a : absint) :=
  (* [Top] really does cover everything. *)
  (forall n, a.(Represents) n a.(Top))

  (* [Join] really does return an upper bound. *)
  /\ (forall x y n, a.(Represents) n x
                    -> a.(Represents) n (a.(Join) x y))
  /\ (forall x y n, a.(Represents) n y
                    -> a.(Represents) n (a.(Join) x y)).

Definition astate (a : absint) := fmap var a.
Definition astates (a : absint) := fmap cmd (astate a).

Inductive compatible a (ss : astates a) (v : valuation) (c : cmd) : Prop :=
| Compatible : forall s,
  ss $? c = Some s
  -> (forall x n xa, v $? x = Some n
                     -> s $? x = Some xa
                     -> a.(Represents) n xa)
  -> compatible ss v c.

Definition merge_astate a : astate a -> astate a -> astate a :=
  merge (fun x y =>
           match x with
           | None => None
           | Some x' =>
             match y with
             | None => None
             | Some y' => Some (a.(Join) x' y')
             end
           end).

Definition merge_astates a : astates a -> astates a -> astates a :=
  merge (fun x y =>
           match x with
           | None => y
           | Some x' =>
             match y with
             | None => Some x'
             | Some y' => Some (merge_astate x' y')
             end
           end).

Inductive oneStepClosure a : astates a -> astates a -> Prop :=
| OscNil :
  oneStepClosure $0 $0
| OscCons : forall ss c s ss' ss'',
  (forall v c' v', step (v, c) (v', c')
    -> compatible ss' v' c')
  -> oneStepClosure ss ss''
  -> oneStepClosure (ss $+ (c, s)) (merge_astates ss' ss'').

Inductive interpret a : astates a -> astates a -> Prop :=
| InterpretDone : forall ss,
  (forall v c, compatible ss v c
               -> forall v' c', step (v, c) (v', c')
                                -> compatible ss v' c')
  -> interpret ss ss

| InterpretStep : forall ss ss' ss'',
  oneStepClosure ss ss'
  -> interpret (merge_astates ss ss') ss''
  -> interpret ss ss''.

Lemma interpret_sound' : forall v c a (ss ss' : astates a),
  interpret ss ss'
  -> ss $? c = Some $0
  -> invariantFor (trsys_of v c) (fun p => compatible ss' (fst p) (snd p)).
Proof.
  induct 1; simplify.

  apply invariant_induction; simplify; propositional; subst; simplify.

  econstructor.
  eassumption.
  simplify.
  equality.

  cases s; cases s'; simplify.
  eapply H.
  eassumption.
  assumption.

  apply IHinterpret.
  unfold merge_astates; simplify.
  rewrite H1.
  cases (ss' $? c); trivial.
  f_equal.
  maps_equal.
  unfold merge_astate; simplify.
  trivial.
Qed.

Theorem interpret_sound : forall v c a (ss : astates a),
  interpret ($0 $+ (c, $0)) ss
  -> invariantFor (trsys_of v c) (fun p => compatible ss (fst p) (snd p)).
Proof.
  simplify.
  eapply interpret_sound'.
  eassumption.
  simplify.
  trivial.
Qed.
