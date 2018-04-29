(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 15: Connecting to Real-World Programming Languages and Platforms
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import FrapWithoutSets SepCancel.
Require Import Arith.Div2.


(** * Some odds and ends from past chapters *)

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).

Ltac simp := repeat (simplify; subst; propositional;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         end); try linear_arithmetic.


(** * Bitvectors of known length *)

Inductive word : nat -> Set :=
| WO : word O
| WS : bool -> forall {n}, word n -> word (S n).

Fixpoint wordToNat {sz} (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false w => 2 * wordToNat w
    | WS true w => S (2 * wordToNat w)
  end.

Fixpoint mod2 (n : nat) : bool :=
  match n with
    | 0 => false
    | 1 => true
    | S (S n') => mod2 n'
  end.

Fixpoint natToWord (sz n : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS (mod2 n) (natToWord sz' (div2 n))
  end.

Definition wzero {sz} := natToWord sz 0.
Definition wone {sz} := natToWord sz 1.
Notation "^" := (natToWord _) (at level 0).

Definition wplus {sz} (w1 w2 : word sz) : word sz :=
  natToWord sz (wordToNat w1 + wordToNat w2).

Infix "^+" := wplus (at level 50, left associativity).

Definition whd {sz} (w : word (S sz)) : bool :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S _ => bool
                             end with
    | WO => tt
    | WS b _ => b
  end.

Definition wtl {sz} (w : word (S sz)) : word sz :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S sz'' => word sz''
                             end with
    | WO => tt
    | WS _ w' => w'
  end.

Lemma shatter_word : forall {n} (a : word n),
  match n return word n -> Prop with
    | O => fun a => a = WO
    | S _ => fun a => a = WS (whd a) (wtl a)
  end a.
Proof.
  destruct a; eauto.
Qed.

Lemma shatter_word_S : forall {n} (a : word (S n)),
  exists b, exists c, a = WS b c.
Proof.
  intros; repeat eexists; apply (shatter_word a).
Qed.
Lemma shatter_word_0 : forall a : word 0,
  a = WO.
Proof.
  intros; apply (shatter_word a).
Qed.

Hint Resolve shatter_word_0.

Require Import Coq.Logic.Eqdep_dec.

Definition weq : forall {sz} (x y : word sz), {x = y} + {x <> y}.
  refine (fix weq sz (x : word sz) : forall y : word sz, {x = y} + {x <> y} :=
    match x in word sz return forall y : word sz, {x = y} + {x <> y} with
      | WO => fun _ => left _ _
      | WS b x' => fun y => if bool_dec b (whd y)
        then if weq _ x' (wtl y) then left _ _ else right _ _
        else right _ _
    end); clear weq.

  symmetry; apply shatter_word_0.

  subst; symmetry; apply (shatter_word y).

  rewrite (shatter_word y); simpl; intro; injection H; intros;
    apply n0; apply inj_pair2_eq_dec in H0; [ auto | apply eq_nat_dec ].

  abstract (rewrite (shatter_word y); simpl; intro; apply n0; injection H; auto).
Defined.


(** * A simple C-like language with just two data types *)

Module Type BIT_WIDTH.
  Parameter bit_width : nat.
End BIT_WIDTH.

Module DeeplyEmbedded(Import BW : BIT_WIDTH).
  Definition wrd := word bit_width.

  Inductive exp :=
  | Var (x : var)

  | Const (n : wrd)
  | Add (x : var) (n : wrd)

  | Head (x : var)
  | Tail (x : var)

  | NotNull (x : var).

  Inductive stmt :=
  | Skip
  | Assign (x : var) (e : exp)
  | WriteHead (x : var) (e : exp)
  | WriteTail (x : var) (e : exp)
  | Seq (s1 s2 : stmt)
  | IfThenElse (e : exp) (s1 s2 : stmt)
  | WhileLoop (e : exp) (s1 : stmt).

  Inductive type :=
  | Scalar
  | ListPointer (t : type).

  Definition type_eq : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
    decide equality.
  Defined.

  Record function := {
    Params : list (var * type);
    Locals : list (var * type);
    Return : type;
    Body : stmt
  }.

  Section fn.
    Variable fn : function.

    Definition vars := Params fn ++ Locals fn ++ [("result", Return fn)].

    Fixpoint varType (x : var) (vs : list (var * type)) : option type :=
      match vs with
      | nil => None
      | (y, t) :: vs' => if y ==v x then Some t else varType x vs'
      end.

    Fixpoint expType (e : exp) : option type :=
      match e with
      | Var x => varType x vars
      | Const _ => Some Scalar
      | Add x _ => match varType x vars with
                   | Some Scalar => Some Scalar
                   | _ => None
                   end
      | Head x => match varType x vars with
                  | Some (ListPointer t) => Some t
                  | _ => None
                  end
      | Tail x => match varType x vars with
                  | Some (ListPointer t) => Some (ListPointer t)
                  | _ => None
                  end
      | NotNull x => match varType x vars with
                     | Some (ListPointer _) => Some Scalar
                     | _ => None
                     end
      end.

    Fixpoint stmtWf (s : stmt) : bool :=
      match s with
      | Skip => true
      | Assign x e => match varType x vars, expType e with
                      | Some t1, Some t2 =>
                        if type_eq t1 t2 then true else false
                      | _, _ => false
                      end
      | WriteHead x e => match varType x vars, expType e with
                         | Some (ListPointer t1), Some t2 =>
                           if type_eq t1 t2 then true else false
                         | _, _ => false
                         end
      | WriteTail x e => match varType x vars, expType e with
                         | Some (ListPointer t1), Some (ListPointer t2) =>
                           if type_eq t1 t2 then true else false
                         | _, _ => false
                         end
      | Seq s1 s2 => stmtWf s1 && stmtWf s2
      | IfThenElse e s1 s2 => match expType e with
                              | Some Scalar => stmtWf s1 && stmtWf s2
                              | _ => false
                              end
      | WhileLoop e s1 => match expType e with
                          | Some Scalar => stmtWf s1
                          | _ => false
                          end
      end.

    Record functionWf : Prop := {
      VarsOk : NoDup (map fst (Params fn ++ Locals fn));
      BodyOk : stmtWf (Body fn) = true
    }.
  End fn.

  Inductive value :=
  | VScalar (n : wrd)
  | VList (p : wrd).

  Definition heap := fmap (wrd) (value * value).
  Definition valuation := fmap var value.

  Inductive eval : heap -> valuation -> exp -> value -> Prop :=
  | VVar : forall H V x v,
      V $? x = Some v
      -> eval H V (Var x) v
  | VConst : forall H V n,
      eval H V (Const n) (VScalar n)
  | VAdd : forall H V x n xn,
      V $? x = Some (VScalar xn)
      -> eval H V (Add x n) (VScalar (xn ^+ n))
  | VHead : forall H V x p ph pt,
      V $? x = Some (VList p)
      -> H $? p = Some (ph, pt)
      -> eval H V (Head x) ph
  | VTail : forall H V x p ph pt,
      V $? x = Some (VList p)
      -> H $? p = Some (ph, pt)
      -> eval H V (Tail x) pt
  | VNotNull : forall H V x p,
      V $? x = Some (VList p)
      -> eval H V (NotNull x) (VScalar (if weq p (^0) then ^1 else ^0)).

  Inductive step : heap * valuation * stmt -> heap * valuation * stmt -> Prop :=
  | StAssign : forall H V x e v,
      eval H V e v
      -> step (H, V, Assign x e) (H, V $+ (x, v), Skip)
  | StWriteHead : forall H V x e a v hv tv,
      V $? x = Some (VList a)
      -> eval H V e v
      -> H $? a = Some (hv, tv)
      -> step (H, V, WriteHead x e) (H $+ (a, (v, tv)), V, Skip)
  | StWriteTail : forall H V x e a v hv tv,
      V $? x = Some (VList a)
      -> eval H V e v
      -> H $? a = Some (hv, tv)
      -> step (H, V, WriteTail x e) (H $+ (a, (hv, v)), V, Skip)
  | StSeq1 : forall H V s2,
      step (H, V, Seq Skip s2) (H, V, s2)
  | StSeq2 : forall H V s1 s2 H' V' s1',
      step (H, V, s1) (H', V', s1')
      -> step (H, V, Seq s1 s2) (H', V', Seq s1' s2)
  | StIfThen : forall H V e s1 s2 n,
      eval H V e (VScalar n)
      -> n <> ^0
      -> step (H, V, IfThenElse e s1 s2) (H, V, s1)
  | StIfElse : forall H V e s1 s2,
      eval H V e (VScalar (^0))
      -> step (H, V, IfThenElse e s1 s2) (H, V, s2)
  | StWhileTrue : forall H V e s1 n,
      eval H V e (VScalar n)
      -> n <> ^0
      -> step (H, V, WhileLoop e s1) (H, V, Seq s1 (WhileLoop e s1))
  | StWhileFalse : forall H V e s1,
      eval H V e (VScalar (^0))
      -> step (H, V, WhileLoop e s1) (H, V, Skip).


  (** * Separation logic for our language *)

  Module Import S <: SEP.
    Definition hprop := heap -> Prop.

    Definition himp (p q : hprop) := forall h, p h -> q h.
    Definition heq (p q : hprop) := forall h, p h <-> q h.

    Definition lift (P : Prop) : hprop :=
      fun h => P /\ h = $0.

    Definition star (p q : hprop) : hprop :=
      fun h => exists h1 h2, split h h1 h2 /\ disjoint h1 h2 /\ p h1 /\ q h2.

    Definition exis {A} (p : A -> hprop) : hprop :=
      fun h => exists x, p x h.

    Notation "[| P |]" := (lift P) : sep_scope.
    Infix "*" := star : sep_scope.
    Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
    Delimit Scope sep_scope with sep.
    Notation "p === q" := (heq p%sep q%sep) (no associativity, at level 70).
    Notation "p ===> q" := (himp p%sep q%sep) (no associativity, at level 70).

    Local Open Scope sep_scope.

    Lemma iff_two : forall A (P Q : A -> Prop),
      (forall x, P x <-> Q x)
      -> (forall x, P x -> Q x) /\ (forall x, Q x -> P x).
    Proof.
      firstorder.
    Qed.

    Local Ltac t := (unfold himp, heq, lift, star, exis; propositional; subst);
                    repeat (match goal with
                            | [ H : forall x, _ <-> _ |- _  ] =>
                              apply iff_two in H
                            | [ H : ex _ |- _ ] => cases H
                            | [ H : split _ _ $0 |- _ ] => apply split_empty_fwd in H
                            end; propositional; subst); eauto 15.

    Theorem himp_heq : forall p q, p === q
      <-> (p ===> q /\ q ===> p).
    Proof.
      t.
    Qed.

    Theorem himp_refl : forall p, p ===> p.
    Proof.
      t.
    Qed.

    Theorem himp_trans : forall p q r, p ===> q -> q ===> r -> p ===> r.
    Proof.
      t.
    Qed.

    Theorem lift_left : forall p (Q : Prop) r,
      (Q -> p ===> r)
      -> p * [| Q |] ===> r.
    Proof.
      t.
    Qed.

    Theorem lift_right : forall p q (R : Prop),
      p ===> q
      -> R
      -> p ===> q * [| R |].
    Proof.
      t.
    Qed.

    Hint Resolve split_empty_bwd'.

    Theorem extra_lift : forall (P : Prop) p,
      P
      -> p === [| P |] * p.
    Proof.
      t.
      apply split_empty_fwd' in H1; subst; auto.
    Qed.    

    Theorem star_comm : forall p q, p * q === q * p.
    Proof.
      t.
    Qed.

    Theorem star_assoc : forall p q r, p * (q * r) === (p * q) * r.
    Proof.
      t.
    Qed.

    Theorem star_cancel : forall p1 p2 q1 q2, p1 ===> p2
      -> q1 ===> q2
      -> p1 * q1 ===> p2 * q2.
    Proof.
      t.
    Qed.

    Theorem exis_gulp : forall A p (q : A -> _),
      p * exis q === exis (fun x => p * q x).
    Proof.
      t.
    Qed.

    Theorem exis_left : forall A (p : A -> _) q,
      (forall x, p x ===> q)
      -> exis p ===> q.
    Proof.
      t.
    Qed.

    Theorem exis_right : forall A p (q : A -> _) x,
      p ===> q x
      -> p ===> exis q.
    Proof.
      t.
    Qed.
  End S.

  Export S.
  Module Import Se := SepCancel.Make(S).

  Definition heap1 (a : wrd) (p : value * value) : heap := $0 $+ (a, p).
  Definition ptsto (a : wrd) (p : value * value) : hprop :=
    fun h => h = heap1 a p.

  (* Helpful notations, some the same as above *)
  Notation "[| P |]" := (lift P) : sep_scope.
  Notation emp := (lift True).
  Infix "*" := star : sep_scope.
  Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
  Delimit Scope sep_scope with sep.
  Notation "p === q" := (heq p%sep q%sep) (no associativity, at level 70).
  Notation "p ===> q" := (himp p%sep q%sep) (no associativity, at level 70).
  Infix "|->" := ptsto (at level 30) : sep_scope.


  (** * Finally, the Hoare logic *)

  Definition hassert := valuation -> hprop.

  Inductive hoare_triple_exp : hassert -> exp -> (value -> hassert) -> Prop :=
  | HtVar : forall x,
      hoare_triple_exp (fun V => exists v, [| V $? x = Some v |])%sep
                       (Var x)
                       (fun r V => [| V $? x = Some r |])%sep
  | HtConst : forall n,
      hoare_triple_exp (fun _ => emp)%sep
                       (Const n)
                       (fun r _ => [| r = VScalar n |])%sep
  | HtAdd : forall x n,
      hoare_triple_exp (fun V => exists xn, [| V $? x = Some (VScalar xn) |])%sep
                       (Add x n)
                       (fun r V => exists xn, [| V $? x = Some (VScalar xn) |]
                                              * [| r = VScalar (xn ^+ n) |])%sep
  | HtHead : forall R x,
      hoare_triple_exp (fun V => exists a, [| V $? x = Some (VList a) |]
                                           * exists p, a |-> p * R p)%sep
                       (Head x)
                       (fun r V => exists a, [| V $? x = Some (VList a) |]
                                             * exists vt, a |-> (r, vt) * R (r, vt))%sep
  | HtTail : forall R x,
      hoare_triple_exp (fun V => exists a, [| V $? x = Some (VList a) |]
                                           * exists p, a |-> p * R p)%sep
                       (Tail x)
                       (fun r V => exists a, [| V $? x = Some (VList a) |]
                                             * exists vh, a |-> (vh, r) * R (vh, r))%sep
  | HtNotNull : forall x,
      hoare_triple_exp (fun V => exists a, [| V $? x = Some (VList a) |])%sep
                       (NotNull x)
                       (fun r V => exists a, [| V $? x = Some (VList a) |]
                                             * [| r = VScalar (if weq a (^0) then ^1 else ^0) |])%sep
  | HtExpConsequence : forall P e Q P' Q',
      hoare_triple_exp P e Q
      -> (forall V, P' V ===> P V)
      -> (forall r V, Q r V ===> Q' r V)
      -> hoare_triple_exp P' e Q'
  | HtExpFrame : forall P e Q R,
      hoare_triple_exp P e Q
      -> hoare_triple_exp (fun V => P V * R V)%sep e (fun r V => Q r V * R V)%sep.

  Fixpoint couldChange (s : stmt) (x : var) : bool :=
    match s with
    | Skip => false
    | Assign y _ => if y ==v x then true else false
    | WriteHead _ _
    | WriteTail _ _ => false
    | Seq s1 s2 => couldChange s1 x || couldChange s2 x
    | IfThenElse _ s1 s2 => couldChange s1 x || couldChange s2 x
    | WhileLoop _ s1 => couldChange s1 x
    end.

  Inductive hoare_triple : hassert -> stmt -> hassert -> Prop :=
  | HtSkip : forall P,
      hoare_triple P Skip P
  | HtAssign : forall P x e Q,
      hoare_triple_exp P e Q
      -> hoare_triple P (Assign x e) (fun V => exists V' r, Q r V' * [| V = V' $+ (x, r) |])%sep
  | HtWriteHead : forall P x e R,
      hoare_triple_exp P e (fun r V => exists a, [| V $? x = Some (VList a) |] * exists vhd vtl, a |-> (vhd, vtl) * R r vhd vtl V)%sep
      -> hoare_triple P
                      (WriteHead x e)
                      (fun V => exists a, [| V $? x = Some (VList a) |] * exists r vhd vtl, a |-> (r, vtl) * R r vhd vtl V)%sep
  | HtWriteTail : forall P x e R,
      hoare_triple_exp P e (fun r V => exists a, [| V $? x = Some (VList a) |] * exists vhd vtl, a |-> (vhd, vtl) * R r vhd vtl V)%sep
      -> hoare_triple P
                      (WriteTail x e)
                      (fun V => exists a, [| V $? x = Some (VList a) |] * exists r vhd vtl, a |-> (vhd, r) * R r vhd vtl V)%sep
  | HtSeq : forall P s1 Q s2 R,
      hoare_triple P s1 Q
      -> hoare_triple Q s2 R
      -> hoare_triple P (Seq s1 s2) R
  | HtIfThenElse : forall P e s1 s2 Q R,
      hoare_triple_exp P e Q
      -> hoare_triple (fun V => exists n, Q (VScalar n) V * [| n <> ^0 |])%sep s1 R
      -> hoare_triple (fun V => Q (VScalar (^0)) V)%sep s2 R
      -> hoare_triple P (IfThenElse e s1 s2) R
  | HtWhileLoop : forall I e s1 Q,
      hoare_triple_exp I e Q
      -> hoare_triple (fun V => exists n, Q (VScalar n) V * [| n <> ^0 |])%sep s1 I
      -> hoare_triple I (WhileLoop e s1) (Q (VScalar (^0)))
  | HtConsequence : forall P s Q P' Q',
      hoare_triple P s Q
      -> (forall V, P' V ===> P V)
      -> (forall V, Q V ===> Q' V)
      -> hoare_triple P' s Q'
  | HtFrame : forall P s Q R,
      hoare_triple P s Q
      -> (forall V1 V2, (forall x, couldChange s x = false
                                   -> V1 $? x = V2 $? x)
                        -> R V1 = R V2)
      -> hoare_triple (fun V => P V * R V)%sep s (fun V => Q V * R V)%sep.

  Notation "{{ V1 ~> P }} c {{ V2 ~> Q }}" :=
    (hoare_triple (fun V1 => P%sep) c (fun V2 => Q%sep)) (at level 90, c at next level).

  Lemma HtStrengthen : forall P s Q Q',
      hoare_triple P s Q
      -> (forall V, Q V ===> Q' V)
      -> hoare_triple P s Q'.
  Proof.
    simplify.
    eapply HtConsequence; eauto.
    reflexivity.
  Qed.

  Lemma HtWeaken : forall P s Q P',
      hoare_triple P s Q
      -> (forall V, P' V ===> P V)
      -> hoare_triple P' s Q.
  Proof.
    simplify.
    eapply HtConsequence; eauto.
    reflexivity.
  Qed.

  Definition trsys_of (H : heap) (V : valuation) (s : stmt) := {|
    Initial := constant [(H, V, s)];
    Step := step
  |}.

  Hint Constructors hoare_triple_exp hoare_triple eval step.

  Lemma eval_subheap : forall H V e r,
      eval H V e r
      -> forall H', (forall a v, H $? a = Some v -> H' $? a = Some v)
                    -> eval H' V e r.
  Proof.
    invert 1; simplify; eauto.
  Qed.

  Lemma drop_cells : forall P e Q,
      hoare_triple_exp P e Q
      -> forall V H r, eval H V e r
                       -> forall H', P V H'
                                     -> (forall a v, H' $? a = Some v -> H $? a = Some v)
                                     -> eval H' V e r.
  Proof.
    induct 1; simplify.

    invert H0; auto.

    invert H0; auto.

    invert H0; auto.

    invert H0.
    invert H1.
    invert H0; simp.
    invert H3.
    apply split_empty_fwd' in H1; subst.
    invert H6.
    invert H1; simp.
    econstructor.
    eassumption.
    cases (x2 $? x0).
    apply H2 in Heq.
    replace p0 with (r, pt) by equality.
    eauto.
    unfold split in H3; subst.
    unfold ptsto in H6; subst.
    unfold heap1 in Heq.
    rewrite lookup_join1 in Heq by (simplify; sets).
    simplify; equality.

    invert H0.
    invert H1.
    invert H0; simp.
    invert H3.
    apply split_empty_fwd' in H1; subst.
    invert H6.
    invert H1; simp.
    econstructor.
    eassumption.
    cases (x2 $? x0).
    apply H2 in Heq.
    replace p0 with (ph, r) by equality.
    eauto.
    unfold split in H3; subst.
    unfold ptsto in H6; subst.
    unfold heap1 in Heq.
    rewrite lookup_join1 in Heq by (simplify; sets).
    simplify; equality.

    invert H0; auto.

    eapply IHhoare_triple_exp; eauto.
    apply H0; auto.

    invert H2; simp.
    eapply IHhoare_triple_exp in H1.
    2: eauto.
    eapply eval_subheap; eauto.
    simplify.
    unfold split in H4; subst.
    rewrite lookup_join1 by eauto using lookup_Some_dom.
    auto.
    simplify.
    unfold split in H4; subst.
    apply H3.
    rewrite lookup_join1 by eauto using lookup_Some_dom.
    auto.
  Qed.

  Lemma preservation_exp : forall P e Q,
      hoare_triple_exp P e Q
      -> forall V H r, P V H -> eval H V e r -> Q r V H.
  Proof.
    induct 1; simplify.

    invert H1.
    cases H0.
    cases H0.
    constructor; assumption.

    invert H1.
    invert H0.
    constructor; reflexivity.

    invert H1.
    invert H0.
    invert H1.
    eexists.
    exists $0, $0; propositional; eauto.
    constructor; eauto.
    constructor; equality.

    invert H1.
    invert H0.
    invert H1.
    simp.
    invert H2.
    invert H5.
    cases x1.
    replace r with v.
    exists x0.
    exists $0, H; propositional; eauto.
    constructor; auto.
    exists v0.
    apply split_empty_fwd' in H0; equality.
    invert H2; simp.
    unfold split in H5; subst.
    unfold ptsto in H6; subst.
    apply split_empty_fwd' in H0; subst.
    replace x0 with p in * by equality.
    unfold heap1 in H7.
    simplify.
    rewrite lookup_join1 in H7.
    simplify; equality.
    simplify; sets.

    invert H1.
    invert H0.
    invert H1.
    simp.
    invert H2.
    invert H5.
    cases x1.
    replace r with v0.
    exists x0.
    exists $0, H; propositional; eauto.
    constructor; auto.
    exists v.
    apply split_empty_fwd' in H0; equality.
    invert H2; simp.
    unfold split in H5; subst.
    unfold ptsto in H6; subst.
    apply split_empty_fwd' in H0; subst.
    replace x0 with p in * by equality.
    unfold heap1 in H7.
    simplify.
    rewrite lookup_join1 in H7.
    simplify; equality.
    simplify; sets.

    invert H1.
    invert H0.
    invert H1.
    exists p, $0, $0; propositional; eauto.
    constructor; auto.
    constructor; auto.

    unfold himp in *; eauto.

    invert H1; simp.
    exists x, x0; propositional; eauto.
    eapply IHhoare_triple_exp; eauto.
    eapply drop_cells; eauto.
    simplify.
    unfold split in H3; subst.
    rewrite lookup_join1 by eauto using lookup_Some_dom.
    auto.
  Qed.

  Opaque heq himp lift star exis ptsto.

  Lemma invert_Assign : forall P x e Q,
    hoare_triple P (Assign x e) Q
    -> exists Q', hoare_triple_exp P e Q'
                  /\ forall V r, Q' r V ===> Q (V $+ (x, r)).
  Proof.
    induct 1; propositional; eauto.

    do 2 eexists.
    eassumption.
    simplify.
    do 2 eapply exis_right.
    cancel.

    first_order.
    do 2 eexists.
    eapply HtExpConsequence.
    eassumption.
    assumption.
    reflexivity.
    etransitivity; eauto.

    first_order.
    do 2 eexists.
    eapply HtExpFrame.
    eassumption.
    simplify.
    rewrite H0 with (V1 := V) (V2 := V $+ (x, r)).
    rewrite H2.
    reflexivity.
    simplify.
    cases (x ==v x1); simplify; equality.
  Qed.

  Lemma invert_WriteHead : forall P x e Q,
    hoare_triple P (WriteHead x e) Q
    -> exists R, hoare_triple_exp P e (fun r V => exists a, [| V $? x = Some (VList a) |] * exists vhd vtl, a |-> (vhd, vtl) * R r vhd vtl V)%sep
                  /\ (forall V, (exists a, [| V $? x = Some (VList a) |] * exists r vhd vtl, a |-> (r, vtl) * R r vhd vtl V) ===> Q V).
  Proof.
    induct 1; first_order; eauto.

    do 2 eexists.
    eassumption.
    reflexivity.

    do 2 eexists.
    eapply HtExpConsequence.
    eassumption.
    assumption.
    simplify.
    reflexivity.
    etransitivity; eauto.

    exists (fun r vhd vtl V => x0 r vhd vtl V * R V)%sep.
    propositional.
    eapply HtExpConsequence with (Q := fun r V =>
                                         ((exists a, [|V $? x = Some (VList a)|]
                                                    * exists vhd vtl, a |-> (vhd, vtl) * x0 r vhd vtl V) * R V)%sep).
    eapply HtExpFrame.
    eassumption.
    reflexivity.
    cancel.
    rewrite <- H2.
    cancel.
  Qed.

  Lemma invert_WriteTail : forall P x e Q,
    hoare_triple P (WriteTail x e) Q
    -> exists R, hoare_triple_exp P e (fun r V => exists a, [| V $? x = Some (VList a) |] * exists vhd vtl, a |-> (vhd, vtl) * R r vhd vtl V)%sep
                  /\ (forall V, (exists a, [| V $? x = Some (VList a) |] * exists r vhd vtl, a |-> (vhd, r) * R r vhd vtl V) ===> Q V).
  Proof.
    induct 1; first_order; eauto.

    do 2 eexists.
    eassumption.
    reflexivity.

    do 2 eexists.
    eapply HtExpConsequence.
    eassumption.
    assumption.
    simplify.
    reflexivity.
    etransitivity; eauto.

    exists (fun r vhd vtl V => x0 r vhd vtl V * R V)%sep.
    propositional.
    eapply HtExpConsequence with (Q := fun r V =>
                                         ((exists a, [|V $? x = Some (VList a)|]
                                                    * exists vhd vtl, a |-> (vhd, vtl) * x0 r vhd vtl V) * R V)%sep).
    eapply HtExpFrame.
    eassumption.
    reflexivity.
    cancel.
    rewrite <- H2.
    cancel.
  Qed.

  Lemma invert_Skip : forall P Q,
    hoare_triple P Skip Q
    -> forall V, P V ===> Q V.
  Proof.
    induct 1; simplify.

    reflexivity.

    do 2 (etransitivity; eauto).

    rewrite IHhoare_triple.
    reflexivity.
  Qed.

  Lemma invert_Seq : forall P s1 s2 Q,
    hoare_triple P (Seq s1 s2) Q
    -> exists R, hoare_triple P s1 R
                 /\ hoare_triple R s2 Q.
  Proof.
    induct 1; simplify; first_order.

    do 2 eexists.
    eapply HtConsequence; eauto; reflexivity.
    eapply HtConsequence; eauto; reflexivity.

    do 2 eexists.
    eapply HtFrame; eauto.
    simplify.
    apply H0.
    simplify.
    apply orb_false_elim in H4; propositional; eauto.
    eapply HtFrame; eauto.
    simplify.
    apply H0.
    simplify.
    apply orb_false_elim in H4; propositional; eauto.
  Qed.

  Lemma invert_IfThenElse : forall P e s1 s2 Q,
    hoare_triple P (IfThenElse e s1 s2) Q
    -> exists R, hoare_triple_exp P e R
                 /\ hoare_triple (fun V => exists n, R (VScalar n) V * [| n <> ^0 |])%sep s1 Q
                 /\ hoare_triple (fun V => R (VScalar (^0)) V)%sep s2 Q.
  Proof.
    induct 1; simplify; first_order.

    eexists; propositional.
    eapply HtExpConsequence.
    eassumption.
    assumption.
    reflexivity.
    eapply HtStrengthen.
    eassumption.
    assumption.
    eapply HtStrengthen.
    eassumption.
    assumption.

    exists (fun r V => x r V * R V)%sep; propositional.
    eauto.
    eapply HtWeaken.
    eapply HtFrame.
    eassumption.
    simplify.
    apply H0.
    simplify.
    apply orb_false_elim in H5; propositional; eauto.
    simplify.
    cancel.
    eapply HtFrame.
    assumption.
    simplify.
    apply H0.
    simplify.
    apply orb_false_elim in H5; propositional; eauto.
  Qed.

  Lemma invert_WhileLoop : forall P e s1 Q,
    hoare_triple P (WhileLoop e s1) Q
    -> exists I R, (forall V, P V ===> I V)
                   /\ hoare_triple_exp I e R
                   /\ hoare_triple (fun V => exists n, R (VScalar n) V * [| n <> ^0 |])%sep s1 I
                   /\ (forall V, R (VScalar (^0)) V ===> Q V).
  Proof.
    induct 1; simplify; first_order.

    do 2 eexists; propositional; eauto; reflexivity.

    exists x, x0; propositional.
    etransitivity; eauto.
    etransitivity; eauto.

    exists (fun V => x V * R V)%sep, (fun r V => x0 r V * R V)%sep; propositional.
    rewrite H1; reflexivity.
    eauto.
    eapply HtWeaken.
    eauto.
    simplify.
    cancel.
    rewrite H4.
    reflexivity.
  Qed.

  Transparent heq himp lift star exis ptsto.

  Lemma preservation : forall s H V s' V' H',
      step (H, V, s) (H', V', s')
      -> forall Q, hoare_triple (fun V' H' => H' = H /\ V' = V) s Q
                   -> hoare_triple (fun V'' H'' => H'' = H' /\ V'' = V') s' Q.
  Proof.
    induct 1; simplify.

    apply invert_Assign in H; simp.
    eapply preservation_exp in H0; eauto.
    eapply HtWeaken.
    auto.
    unfold himp; simplify.
    propositional; subst.
    apply H2; assumption.
    simplify; auto.

    apply invert_WriteHead in H3; simp.
    eapply preservation_exp in H1; eauto.
    simplify.
    eapply HtWeaken.
    auto.
    unfold himp; simplify.
    propositional; subst.
    apply H5.
    invert H1.
    invert H4; simp.
    invert H6.
    invert H8.
    invert H6.
    invert H8; simp.
    invert H9.
    exists x1.
    apply split_empty_fwd' in H1; subst.
    exists $0, (x3 $+ (a, (v, tv))); propositional; eauto.
    constructor; auto.
    exists v, x2, tv.
    exists (heap1 x1 (v, tv)), x6; propositional; eauto.
    unfold split, heap1.
    unfold split, heap1 in H6.
    subst.
    apply fmap_ext; simplify.
    cases (weq k x1); subst.
    replace x1 with a by equality.
    repeat (rewrite lookup_join1 by (simplify; sets); simplify).
    auto.
    simplify.
    repeat (rewrite lookup_join2 by (simplify; sets); simplify).
    auto.
    unfold disjoint, heap1 in *.
    intros.
    apply H8 with a0.
    cases (weq x1 a0); subst; simplify.
    equality.
    assumption.
    assumption.
    constructor.
    unfold split in H6; subst.
    replace x1 with a in * by equality.
    unfold heap1 in H2.
    rewrite lookup_join1 in H2 by (simplify; sets).
    simplify.
    equality.
    simplify; auto.

    apply invert_WriteTail in H3; simp.
    eapply preservation_exp in H1; eauto.
    simplify.
    eapply HtWeaken.
    auto.
    unfold himp; simplify.
    propositional; subst.
    apply H5.
    invert H1.
    invert H4; simp.
    invert H6.
    invert H8.
    invert H6.
    invert H8; simp.
    invert H9.
    exists x1.
    apply split_empty_fwd' in H1; subst.
    exists $0, (x3 $+ (a, (hv, v))); propositional; eauto.
    constructor; auto.
    exists v, hv, x4.
    exists (heap1 x1 (hv, v)), x6; propositional; eauto.
    unfold split, heap1.
    unfold split, heap1 in H6.
    subst.
    apply fmap_ext; simplify.
    cases (weq k x1); subst.
    replace x1 with a by equality.
    repeat (rewrite lookup_join1 by (simplify; sets); simplify).
    auto.
    simplify.
    repeat (rewrite lookup_join2 by (simplify; sets); simplify).
    auto.
    unfold disjoint, heap1 in *.
    intros.
    apply H8 with a0.
    cases (weq x1 a0); subst; simplify.
    equality.
    assumption.
    assumption.
    constructor.
    unfold split in H6; subst.
    replace x1 with a in * by equality.
    unfold heap1 in H2.
    rewrite lookup_join1 in H2 by (simplify; sets).
    simplify.
    equality.
    simplify; auto.

    apply invert_Seq in H; first_order.
    eapply HtWeaken.
    eauto.
    simplify.
    eapply invert_Skip in H; eassumption.

    apply invert_Seq in H1; first_order.
    eauto.

    apply invert_IfThenElse in H; first_order.
    eapply HtWeaken; eauto.
    simplify.
    unfold himp; propositional; subst.
    eapply preservation_exp in H0; eauto.
    exists n, H', $0; propositional; eauto.
    constructor; auto.
    simplify; auto.

    apply invert_IfThenElse in H; first_order.
    eapply HtWeaken; eauto.
    simplify.
    unfold himp; propositional; subst.
    eapply preservation_exp in H0; eauto.
    simplify; auto.

    apply invert_WhileLoop in H; first_order.
    eapply HtSeq.
    eapply HtWeaken; eauto.
    simplify.
    unfold himp; propositional; subst.
    eapply preservation_exp in H0; eauto.
    exists n, H', $0; propositional; eauto.
    constructor; auto.
    apply H; simplify; auto.
    eapply HtStrengthen.
    eauto.
    eauto.

    apply invert_WhileLoop in H; first_order.
    eapply HtWeaken; eauto.
    simplify.
    unfold himp; propositional; subst.
    eapply preservation_exp in H0; eauto.
    apply H3; auto.
    apply H; simplify; auto.
  Qed.

  Lemma hoare_triple_sound' : forall P s Q,
      hoare_triple P s Q
      -> forall H V, P V H
      -> invariantFor (trsys_of H V s)
                      (fun p => hoare_triple (fun V' H' => H' = fst (fst p) /\ V' = snd (fst p))
                                             (snd p)
                                             Q).
  Proof.
    simplify.

    apply invariant_induction; simplify.

    propositional; subst; simplify.
    eapply HtWeaken.
    eauto.
    unfold himp; simplify; equality.

    cases s0.
    cases p.
    cases s'.
    cases p.
    simplify.
    eapply preservation; eauto.
  Qed.

  Theorem hoare_triple_sound : forall P s Q,
      hoare_triple P s Q
      -> forall H V, P V H
      -> invariantFor (trsys_of H V s)
                      (fun p => (snd p = Skip /\ Q (snd (fst p)) (fst (fst p)))
                                \/ exists p', step p p').
  Proof.
    simplify.
    eapply invariant_weaken.
    eapply hoare_triple_sound'; eauto.
    simplify.
  Admitted.

End DeeplyEmbedded.
