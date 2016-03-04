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
  Const : nat -> Typeof;
  (* Most accurate representation of a constant *)
  Join : Typeof -> Typeof -> Typeof;
  (* Least upper bound of two elements *)
  Represents : nat -> Typeof -> Prop
  (* Which lattice elements represent which numbers? *)
}.

Definition absint_sound (a : absint) :=
  (* [Const] gives accurate answers. *)
  (forall n, a.(Represents) n (a.(Const) n))

  (* [Join] really does return an upper bound. *)
  /\ (forall x y n, a.(Represents) n x
                    -> a.(Represents) n (a.(Join) x y))
  /\ (forall x y n, a.(Represents) n y
                    -> a.(Represents) n (a.(Join) x y)).

Definition astate (a : absint) := fmap var a.
Definition astates (a : absint) := fmap cmd (astate a).

Definition compatible1 a (s : astate a) (v : valuation) (c : cmd) : Prop :=
  forall x n xa, v $? x = Some n
                 -> s $? x = Some xa
                 -> a.(Represents) n xa.

Inductive compatible a (ss : astates a) (v : valuation) (c : cmd) : Prop :=
| Compatible : forall s,
  ss $? c = Some s
  -> compatible1 s v c
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
    -> compatible1 s v c
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
  unfold compatible1.
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


(** * Example: even-odd analysis *)

Inductive parity := Even | Odd | Either.

Definition isEven (n : nat) := exists k, n = k * 2.
Definition isOdd (n : nat) := exists k, n = k * 2 + 1.

Theorem decide_parity : forall n, isEven n \/ isOdd n.
Proof.
  induct n; simplify; propositional.

  left; exists 0; linear_arithmetic.

  invert H.
  right.
  exists x; linear_arithmetic.

  invert H.
  left.
  exists (x + 1); linear_arithmetic.
Qed.
  
Theorem notEven_odd : forall n, ~isEven n -> isOdd n.
Proof.
  simplify.
  assert (isEven n \/ isOdd n).
  apply decide_parity.
  propositional.
Qed.  

Theorem isEven_0 : isEven 0.
Proof.
  exists 0; linear_arithmetic.
Qed.

Theorem isEven_1 : ~isEven 1.
Proof.
  propositional; invert H; linear_arithmetic.
Qed.

Theorem isEven_S_Even : forall n, isEven n -> ~isEven (S n).
Proof.
  propositional; invert H; invert H0; linear_arithmetic.
Qed.

Theorem isEven_S_Odd : forall n, ~isEven n -> isEven (S n).
Proof.
  propositional.
  apply notEven_odd in H.
  invert H.
  exists (x + 1); linear_arithmetic.
Qed.

Hint Resolve isEven_0 isEven_1 isEven_S_Even isEven_S_Odd.  

Definition parity_flip (p : parity) :=
  match p with
  | Even => Odd
  | Odd => Even
  | Either => Either
  end.

Fixpoint parity_const (n : nat) :=
  match n with
  | O => Even
  | S n' => parity_flip (parity_const n')
  end.

Definition parity_join (x y : parity) :=
  match x, y with
  | Even, Even => Even
  | Odd, Odd => Odd
  | _, _ => Either
  end.

Inductive parity_rep : nat -> parity -> Prop :=
| PrEven : forall n,
  isEven n
  -> parity_rep n Even
| PrOdd : forall n,
  ~isEven n
  -> parity_rep n Odd
| PrEither : forall n,
  parity_rep n Either.

Hint Constructors parity_rep.

Definition parity_absint := {|
  Const := parity_const;
  Join := parity_join;
  Represents := parity_rep
|}.

Lemma parity_const_sound : forall n,
  parity_rep n (parity_const n).
Proof.
  induct n; simplify; eauto.
  cases (parity_const n); simplify; eauto.
  invert IHn; eauto.
  invert IHn; eauto.
Qed.

Hint Resolve parity_const_sound.

Theorem parity_sound : absint_sound parity_absint.
Proof.
  unfold absint_sound; propositional.

  simplify; eauto.

  invert H; cases y; simplify; eauto.

  invert H; cases x; simplify; eauto.
Qed.

Definition loopy :=
  "n" <- 100;;
  "a" <- 0;;
  while "n" loop
    "a" <- "a" + "n";;
    "n" <- "n" - 2
  done.

Theorem compatible_skip : forall (s : astate parity_absint) v c c' m,
  compatible1 s v c
  -> compatible (m $+ (c', s)) v c'.
Proof.
  unfold compatible1; simplify.
  econstructor.
  simplify; equality.
  auto.
Qed.

Theorem compatible_skip2 : forall (s : astate parity_absint) v c c' m c'' s',
  compatible1 s v c
  -> c'' <> c'
  -> compatible (m $+ (c', s) $+ (c'', s')) v c'.
Proof.
  unfold compatible1; simplify.
  econstructor.
  simplify; equality.
  auto.
Qed.

Theorem compatible_const : forall (s : astate parity_absint) v c c' x n,
  compatible1 s v c
  -> compatible ($0 $+ (c', s $+ (x, parity_const n))) (v $+ (x, n)) c'.
Proof.
  unfold compatible1; simplify.
  econstructor.
  simplify; equality.
  unfold compatible1.
  simplify.
  cases (x ==v x0); simplify.
  invert H1.
  invert H0.
  eauto.

  eapply H.
  eassumption.
  assumption.
Qed.

Hint Rewrite merge_empty1 merge_empty2 using solve [ eauto 1 ].
Hint Rewrite merge_empty1_alt merge_empty2_alt using congruence.

Lemma merge_astates_fok : forall x : option (astate parity_absint),
  match x with Some x' => Some x' | None => None end = x.
Proof.
  simplify; cases x; equality.
Qed.

Lemma merge_astates_fok2 : forall x (y : option (astate parity_absint)),
    match y with
    | Some y' => Some (merge_astate x y')
    | None => Some x
    end = None -> False.
Proof.
  simplify; cases y; equality.
Qed.

Hint Resolve merge_astates_fok merge_astates_fok2.

Hint Rewrite merge_add1 using solve [ eauto | unfold Sets.In; simplify; equality ].
Hint Rewrite merge_add1_alt using solve [ congruence | unfold Sets.In; simplify; equality ].

Ltac inList x xs :=
  match xs with
  | (x, _) => constr:true
  | (_, ?xs') => inList x xs'
  | _ => constr:false
  end.

Ltac maybe_simplify_map m found kont :=
  match m with
  | @empty ?A ?B => kont (@empty A B)
  | ?m' $+ (?k, ?v) =>
    let iL := inList k found in
    match iL with
    | true => maybe_simplify_map m' found kont
    | false =>
      maybe_simplify_map m' (k, found) ltac:(fun m' => kont (m' $+ (k, v)))
    end
  end.

Ltac simplify_map' m found kont :=
  match m with
  | ?m' $+ (?k, ?v) =>
    let iL := inList k found in
      match iL with
      | true => maybe_simplify_map m' found kont
      | false =>
        simplify_map' m' (k, found) ltac:(fun m' => kont (m' $+ (k, v)))
      end
  end.

Ltac simplify_map :=
  match goal with
  | [ |- context[?m $+ (?k, ?v)] ] =>
    simplify_map' (m $+ (k, v)) tt ltac:(fun m' =>
                                           replace (m $+ (k, v)) with m' by maps_equal)
  end.

Definition easy :=
  "n" <- 10;;
  while "n" loop
    "n" <- "n" - 2
  done.

Theorem easy_even : forall v n,
  isEven n
  -> invariantFor (trsys_of v easy) (fun p => exists n, fst p $? "n" = Some n /\ isEven n).
Proof.
  simplify.
  eapply invariant_weaken.

  unfold easy.
  apply interpret_sound.

  Ltac interpret1 :=
    eapply InterpretStep; [ (repeat (apply OscNil || eapply OscCons);
                              invert 1; repeat (match goal with
                                                | [ H : step _ _ |- _ ] => invert H
                                                | [ _ : match ?E with
                                                        | Some n => n
                                                        | None => 0
                                                        end = 0 |- _ ] => cases E; try linear_arithmetic
                                                end; simplify); simplify;
                              try solve [ eapply compatible_skip; eassumption
                                        | eapply compatible_skip2; eassumption || congruence
                                        | eapply compatible_const; eassumption ]) | ];
    repeat match goal with
           | [ |- context[@add ?A ?B ?m _ _] ] =>
             match m with
             | @empty _ _ => fail 1
             | _ => unify m (@empty A B)
             end
           end.

  interpret1.
  unfold merge_astates, merge_astate; simplify.
  interpret1.
  unfold merge_astates, merge_astate; simplify.
  simplify_map.
  interpret1.
  unfold merge_astates, merge_astate; simplify.
  simplify_map.
  interpret1.
