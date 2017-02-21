(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 8: Abstract Interpretation and Dataflow Analysis
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap Imp.
Export Imp.

Set Implicit Arguments.


(* Reduced version of code from AbstractInterpretation.v *)

Record absint := {
  Domain :> Set;
  Top : Domain;
  Constant : nat -> Domain;
  Add : Domain -> Domain -> Domain;
  Subtract : Domain -> Domain -> Domain;
  Multiply : Domain -> Domain -> Domain;
  Join : Domain -> Domain -> Domain;
  Represents : nat -> Domain -> Prop
}.

Record absint_sound (a : absint) : Prop := {
  TopSound : forall n, a.(Represents) n a.(Top);

  ConstSound : forall n, a.(Represents) n (a.(Constant) n);

  AddSound : forall n na m ma, a.(Represents) n na
                               -> a.(Represents) m ma
                               -> a.(Represents) (n + m) (a.(Add) na ma);
  SubtractSound: forall n na m ma, a.(Represents) n na
                                   -> a.(Represents) m ma
                                   -> a.(Represents) (n - m) (a.(Subtract) na ma);
  MultiplySound : forall n na m ma, a.(Represents) n na
                                    -> a.(Represents) m ma
                                    -> a.(Represents) (n * m) (a.(Multiply) na ma);

  AddMonotone : forall na na' ma ma', (forall n, a.(Represents) n na -> a.(Represents) n na')
                                      -> (forall n, a.(Represents) n ma -> a.(Represents) n ma')
                                      -> (forall n, a.(Represents) n (a.(Add) na ma)
                                                    -> a.(Represents) n (a.(Add) na' ma'));
  SubtractMonotone : forall na na' ma ma', (forall n, a.(Represents) n na -> a.(Represents) n na')
                                           -> (forall n, a.(Represents) n ma -> a.(Represents) n ma')
                                           -> (forall n, a.(Represents) n (a.(Subtract) na ma)
                                                         -> a.(Represents) n (a.(Subtract) na' ma'));
  MultiplyMonotone : forall na na' ma ma', (forall n, a.(Represents) n na -> a.(Represents) n na')
                                           -> (forall n, a.(Represents) n ma -> a.(Represents) n ma')
                                           -> (forall n, a.(Represents) n (a.(Multiply) na ma)
                                                         -> a.(Represents) n (a.(Multiply) na' ma'));

  JoinSoundLeft : forall x y n, a.(Represents) n x
                                -> a.(Represents) n (a.(Join) x y);
  JoinSoundRight : forall x y n, a.(Represents) n y
                                 -> a.(Represents) n (a.(Join) x y)
}.

Hint Resolve TopSound ConstSound AddSound SubtractSound MultiplySound
     AddMonotone SubtractMonotone MultiplyMonotone
     JoinSoundLeft JoinSoundRight.



Definition astate (a : absint) := fmap var a.

Fixpoint absint_interp (e : arith) a (s : astate a) : a :=
  match e with
  | Const n => a.(Constant) n
  | Var x => match s $? x with
             | None => a.(Top)
             | Some xa => xa
             end
  | Plus e1 e2 => a.(Add) (absint_interp e1 s) (absint_interp e2 s)
  | Minus e1 e2 => a.(Subtract) (absint_interp e1 s) (absint_interp e2 s)
  | Times e1 e2 => a.(Multiply) (absint_interp e1 s) (absint_interp e2 s)
  end.

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

Definition subsumed a (s1 s2 : astate a) :=
  forall x, match s1 $? x with
            | None => s2 $? x = None
            | Some xa1 =>
              forall xa2, s2 $? x = Some xa2
                          -> forall n, a.(Represents) n xa1
                                       -> a.(Represents) n xa2
            end.

Theorem subsumed_refl : forall a (s : astate a),
  subsumed s s.
Proof.
  unfold subsumed; simplify.
  cases (s $? x); equality.
Qed.

Hint Resolve subsumed_refl.

Lemma subsumed_use : forall a (s s' : astate a) x n t0 t,
  s $? x = Some t0
  -> subsumed s s'
  -> s' $? x = Some t
  -> Represents a n t0
  -> Represents a n t.
Proof.
  unfold subsumed; simplify.
  specialize (H0 x).
  rewrite H in H0.
  eauto.
Qed.

Lemma subsumed_use_empty : forall a (s s' : astate a) x n t0 t,
  s $? x = None
  -> subsumed s s'
  -> s' $? x = Some t
  -> Represents a n t0
  -> Represents a n t.
Proof.
  unfold subsumed; simplify.
  specialize (H0 x).
  rewrite H in H0.
  equality.
Qed.

Hint Resolve subsumed_use subsumed_use_empty.

Lemma subsumed_trans : forall a (s1 s2 s3 : astate a),
  subsumed s1 s2
  -> subsumed s2 s3
  -> subsumed s1 s3.
Proof.
  unfold subsumed; simplify.
  specialize (H x); specialize (H0 x).
  cases (s1 $? x); simplify.
  cases (s2 $? x); eauto.
  cases (s2 $? x); eauto.
  equality.
Qed.

Lemma subsumed_merge_left : forall a, absint_sound a
  -> forall s1 s2 : astate a,
    subsumed s1 (merge_astate s1 s2).
Proof.
  unfold subsumed, merge_astate; simplify.
  cases (s1 $? x); trivial.
  cases (s2 $? x); simplify; try equality.
  invert H0; eauto.
Qed.

Hint Resolve subsumed_merge_left.

Lemma subsumed_add : forall a, absint_sound a
  -> forall (s1 s2 : astate a) x v1 v2,
  subsumed s1 s2
  -> (forall n, a.(Represents) n v1 -> a.(Represents) n v2)
  -> subsumed (s1 $+ (x, v1)) (s2 $+ (x, v2)).
Proof.
  unfold subsumed; simplify.
  cases (x ==v x0); subst; simplify; eauto.
  invert H2; eauto.
  specialize (H0 x0); eauto.
Qed.

Hint Resolve subsumed_add.


(** * Flow-sensitive analysis *)

Definition compatible a (s : astate a) (v : valuation) : Prop :=
  forall x xa, s $? x = Some xa
               -> exists n, v $? x = Some n
                            /\ a.(Represents) n xa.

Lemma compatible_add : forall a (s : astate a) v x na n,
  compatible s v
  -> a.(Represents) n na
  -> compatible (s $+ (x, na)) (v $+ (x, n)).
Proof.
  unfold compatible; simplify.
  cases (x ==v x0); simplify; eauto.
  invert H1; eauto.
Qed.

Hint Resolve compatible_add.

(* A similar result follows about soundness of expression interpretation. *)
Theorem absint_interp_ok : forall a, absint_sound a
  -> forall (s : astate a) v e,
    compatible s v
    -> a.(Represents) (interp e v) (absint_interp e s).
Proof.
  induct e; simplify; eauto.
  cases (s $? x); auto.
  unfold compatible in H0.
  apply H0 in Heq.
  invert Heq.
  propositional.
  rewrite H2.
  assumption.
Qed.

Hint Resolve absint_interp_ok.

Definition astates (a : absint) := fmap cmd (astate a).

Fixpoint absint_step a (s : astate a) (c : cmd) (wrap : cmd -> cmd) : option (astates a) :=
  match c with
  | Skip => None
  | Assign x e => Some ($0 $+ (wrap Skip, s $+ (x, absint_interp e s)))
  | Sequence c1 c2 =>
    match absint_step s c1 (fun c => wrap (Sequence c c2)) with
    | None => Some ($0 $+ (wrap c2, s))
    | v => v
    end
  | If _ then_ else_ => Some ($0 $+ (wrap then_, s) $+ (wrap else_, s))
  | While e body => Some ($0 $+ (wrap Skip, s) $+ (wrap (Sequence body (While e body)), s))
  end.

Lemma command_equal : forall c1 c2 : cmd, sumbool (c1 = c2) (c1 <> c2).
Proof.
  repeat decide equality.
Qed.

Theorem absint_step_ok : forall a, absint_sound a
  -> forall (s : astate a) v, compatible s v
  -> forall c v' c', step (v, c) (v', c')
                     -> forall wrap, exists ss s', absint_step s c wrap = Some ss
                                                   /\ ss $? wrap c' = Some s'
                                                   /\ compatible s' v'.
Proof.
  induct 2; simplify.

  do 2 eexists; propositional.
  simplify; equality.
  eauto.

  eapply IHstep in H0; auto.
  invert H0.
  invert H2.
  propositional.
  rewrite H2.
  eauto.

  do 2 eexists; propositional.
  simplify; equality.
  assumption.

  do 2 eexists; propositional.
  cases (command_equal (wrap c') (wrap else_)).
  simplify; equality.
  simplify; equality.
  assumption.

  do 2 eexists; propositional.
  simplify; equality.
  assumption.

  do 2 eexists; propositional.
  simplify; equality.
  assumption.

  do 2 eexists; propositional.
  cases (command_equal (wrap Skip) (wrap (body;; while e loop body done))).
  simplify; equality.
  simplify; equality.
  assumption.
Qed.

Inductive abs_step a : astate a * cmd -> astate a * cmd -> Prop :=
| AbsStep : forall s c ss s' c',
  absint_step s c (fun x => x) = Some ss
  -> ss $? c' = Some s'
  -> abs_step (s, c) (s', c').

Hint Constructors abs_step.

Definition absint_trsys a (c : cmd) := {|
  Initial := {($0, c)};
  Step := abs_step (a := a)
|}.

Inductive Rabsint a : valuation * cmd -> astate a * cmd -> Prop :=
| RAbsint : forall v s c,
  compatible s v
  -> Rabsint (v, c) (s, c).

Hint Constructors abs_step Rabsint.

Theorem absint_simulates : forall a v c,
  absint_sound a
  -> simulates (Rabsint (a := a)) (trsys_of v c) (absint_trsys a c).
Proof.
  simplify.
  constructor; simplify.

  exists ($0, c); propositional.
  subst.
  constructor.
  unfold compatible.
  simplify.
  equality.

  invert H0.
  cases st1'.
  eapply absint_step_ok in H1; eauto.
  invert H1.
  invert H0.
  propositional.
  eauto.
Qed.

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
  oneStepClosure ss ss'
  -> match absint_step s c (fun x => x) with
     | None => ss'
     | Some ss'' => merge_astates ss'' ss'
     end = ss''
  -> oneStepClosure (ss $+ (c, s)) ss''.

Definition subsumeds a (ss1 ss2 : astates a) :=
  forall c s1, ss1 $? c = Some s1
               -> exists s2, ss2 $? c = Some s2
                             /\ subsumed s1 s2.

Theorem subsumeds_refl : forall a (ss : astates a),
  subsumeds ss ss.
Proof.
  unfold subsumeds; simplify; eauto.
Qed.

Hint Resolve subsumeds_refl.

Lemma subsumeds_add : forall a (ss1 ss2 : astates a) c s1 s2,
  subsumeds ss1 ss2
  -> subsumed s1 s2
  -> subsumeds (ss1 $+ (c, s1)) (ss2 $+ (c, s2)).
Proof.
  unfold subsumeds; simplify.
  cases (command_equal c c0); subst; simplify; eauto.
  invert H1; eauto.
Qed.

Hint Resolve subsumeds_add.

Lemma subsumeds_empty : forall a (ss : astates a),
  subsumeds $0 ss.
Proof.
  unfold subsumeds; simplify.
  equality.
Qed.

Lemma subsumeds_add_left : forall a (ss1 ss2 : astates a) c s,
  ss2 $? c = Some s
  -> subsumeds ss1 ss2
  -> subsumeds (ss1 $+ (c, s)) ss2.
Proof.
  unfold subsumeds; simplify.
  cases (command_equal c c0); subst; simplify; eauto.
  invert H1; eauto.
Qed.

Inductive interpret a : astates a -> astates a -> astates a -> Prop :=
| InterpretDone : forall ss1 any ss2,
  oneStepClosure ss1 ss2
  -> subsumeds ss2 ss1
  -> interpret ss1 any ss1
| InterpretStep : forall ss worklist ss' ss'',
  oneStepClosure worklist ss'
  -> interpret (merge_astates ss ss') ss' ss''
  -> interpret ss worklist ss''.

Lemma oneStepClosure_sound : forall a, absint_sound a
  -> forall ss ss' : astates a, oneStepClosure ss ss'
  -> forall c s s' c', ss $? c = Some s
                       -> abs_step (s, c) (s', c')
                          -> exists s'', ss' $? c' = Some s''
                                         /\ subsumed s' s''.
Proof.
  induct 2; simplify.

  equality.

  cases (command_equal c c0); subst; simplify.

  invert H2.
  invert H3.
  rewrite H5.
  unfold merge_astates; simplify.
  rewrite H7.
  cases (ss' $? c').
  eexists; propositional.
  unfold subsumed; simplify.
  unfold merge_astate; simplify.
  cases (s' $? x); try equality.
  cases (a0 $? x); simplify; try equality.
  invert H1; eauto.
  eauto.

  apply IHoneStepClosure in H3; auto.
  invert H3; propositional.
  cases (absint_step s c (fun x => x)); eauto.
  unfold merge_astates; simplify.
  rewrite H3.
  cases (a0 $? c'); eauto.
  eexists; propositional.
  unfold subsumed; simplify.
  unfold merge_astate; simplify.
  specialize (H4 x0).
  cases (s' $? x0).
  cases (a1 $? x0); try equality.
  cases (x $? x0); try equality.
  invert 1.
  eauto.

  rewrite H4.
  cases (a1 $? x0); equality.
Qed.

Lemma absint_step_monotone_None : forall a (s : astate a) c wrap,
    absint_step s c wrap = None
    -> forall s' : astate a, absint_step s' c wrap = None.
Proof.
  induct c; simplify; try equality.
  cases (absint_step s c1 (fun c => wrap (c;; c2))); equality.
Qed.

Lemma absint_interp_monotone : forall a, absint_sound a
  -> forall (s : astate a) e s' n,
    a.(Represents) n (absint_interp e s)
    -> subsumed s s'
    -> a.(Represents) n (absint_interp e s').
Proof.
  induct e; simplify; eauto.

  cases (s' $? x); eauto.
  cases (s $? x); eauto.
Qed.

Hint Resolve absint_interp_monotone.

Lemma absint_step_monotone : forall a, absint_sound a
    -> forall (s : astate a) c wrap ss,
      absint_step s c wrap = Some ss
      -> forall s', subsumed s s'
                    -> exists ss', absint_step s' c wrap = Some ss'
                                   /\ subsumeds ss ss'.
Proof.
  induct c; simplify.

  equality.

  invert H0.
  eexists; propositional.
  eauto.
  apply subsumeds_add; eauto.

  cases (absint_step s c1 (fun c => wrap (c;; c2))).

  invert H0.
  eapply IHc1 in Heq; eauto.
  invert Heq; propositional.
  rewrite H2; eauto.

  invert H0.
  eapply absint_step_monotone_None in Heq; eauto.
  rewrite Heq; eauto.

  invert H0; eauto.

  invert H0; eauto.
Qed.

Lemma abs_step_monotone : forall a, absint_sound a
  -> forall (s : astate a) c s' c',
    abs_step (s, c) (s', c')
    -> forall s1, subsumed s s1
                  -> exists s1', abs_step (s1, c) (s1', c')
                                 /\ subsumed s' s1'.
Proof.
  invert 2; simplify.
  eapply absint_step_monotone in H4; eauto.
  invert H4; propositional.
  apply H3 in H6.
  invert H6; propositional; eauto.
Qed.

Lemma interpret_sound' : forall c a, absint_sound a
  -> forall ss worklist ss' : astates a, interpret ss worklist ss'
    -> ss $? c = Some $0
    -> invariantFor (absint_trsys a c) (fun p => exists s, ss' $? snd p = Some s
                                                           /\ subsumed (fst p) s).
Proof.
  induct 2; simplify; subst.

  apply invariant_induction; simplify; propositional; subst; simplify; eauto.

  invert H3; propositional.
  cases s.
  cases s'.
  simplify.
  eapply abs_step_monotone in H4; eauto.
  invert H4; propositional.
  eapply oneStepClosure_sound in H4; eauto.
  invert H4; propositional.
  eapply H1 in H4.
  invert H4; propositional.
  eauto using subsumed_trans.

  apply IHinterpret.
  unfold merge_astates; simplify.
  rewrite H2.
  cases (ss' $? c); trivial.
  unfold merge_astate; simplify; equality.
Qed.

Theorem interpret_sound : forall c a (ss : astates a),
  absint_sound a
  -> interpret ($0 $+ (c, $0)) ($0 $+ (c, $0)) ss
  -> invariantFor (absint_trsys a c) (fun p => exists s, ss $? snd p = Some s
                                                         /\ subsumed (fst p) s).
Proof.
  simplify.
  eapply interpret_sound'; eauto.
  simplify; equality.
Qed.

Ltac interpret_simpl := unfold merge_astates, merge_astate;
                       simplify; repeat simplify_map.
Ltac oneStepClosure := apply OscNil
                       || (eapply OscCons; [ oneStepClosure
                                           | interpret_simpl; reflexivity ]).
Ltac interpret1 := eapply InterpretStep; [ oneStepClosure | interpret_simpl ].
Ltac interpret_done := eapply InterpretDone; [ oneStepClosure
  | repeat (apply subsumeds_add_left || apply subsumeds_empty); (simplify; equality) ].
