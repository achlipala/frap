Require Import Frap.


(** * Evaluation Contexts for Lambda Calculus *)

Module Stlc.
  Inductive exp : Set :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp).

  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1).

  Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
    match e2 with
      | Var y => if y ==v x then e1 else Var y
      | Const n => Const n
      | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
      | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
      | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
    end.

  (* Here's the first difference from last chapter. *)
  Inductive context : Set :=
  | Hole : context
  | Plus1 : context -> exp -> context
  | Plus2 : exp -> context -> context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context.

  (* Again, note how two of the rules include [value] premises. *)
  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugPlus1 : forall e e' C e2,
    plug C e e'
    -> plug (Plus1 C e2) e (Plus e' e2)
  | PlugPlus2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Plus2 v1 C) e (Plus v1 e')
  | PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e').

  (* Small-step, call-by-value evaluation, using our evaluation contexts *)

  (* First: the primitive reductions *)
  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
    step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2)).

  (* Then: running them in context *)
  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

  (* It's easy to wrap everything as a transition system. *)
  Definition trsys_of (e : exp) := {|
    Initial := {e};
    Step := step
  |}.


  (* Typing details are the same as last chapter. *)
  Inductive type :=
  | Nat                  (* Numbers *)
  | Fun (dom ran : type) (* Functions *).

  Inductive has_ty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
    G $? x = Some t
    -> has_ty G (Var x) t
  | HtConst : forall G n,
    has_ty G (Const n) Nat
  | HtPlus : forall G e1 e2,
    has_ty G e1 Nat
    -> has_ty G e2 Nat
    -> has_ty G (Plus e1 e2) Nat
  | HtAbs : forall G x e1 t1 t2,
    has_ty (G $+ (x, t1)) e1 t2
    -> has_ty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
    has_ty G e1 (Fun t1 t2)
    -> has_ty G e2 t1
    -> has_ty G (App e1 e2) t2.

  Local Hint Constructors value plug step0 step has_ty : core.

  (** * Now we adapt the automated proof of type soundness. *)

  Ltac t0 := match goal with
             | [ H : ex _ |- _ ] => invert H
             | [ H : _ /\ _ |- _ ] => invert H
             | [ |- context[?x ==v ?y] ] => cases (x ==v y)
             | [ H : Some _ = Some _ |- _ ] => invert H

             | [ H : step _ _ |- _ ] => invert H
             | [ H : step0 _ _ |- _ ] => invert1 H
             | [ H : has_ty _ ?e _, H' : value ?e |- _ ] => invert H'; invert H
             | [ H : has_ty _ _ _ |- _ ] => invert1 H
             | [ H : plug _ _ _ |- _ ] => invert1 H
             end; subst.

  Ltac t := simplify; propositional; repeat (t0; simplify); try equality; eauto 6.

  Lemma progress : forall e t,
    has_ty $0 e t
    -> value e
    \/ (exists e' : exp, step e e').
  Proof.
    induct 1; t.
  Qed.

  Lemma weakening_override : forall (G G' : fmap var type) x t,
    (forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
    -> (forall x' t', G $+ (x, t) $? x' = Some t'
                      -> G' $+ (x, t) $? x' = Some t').
  Proof.
    simplify.
    cases (x ==v x'); simplify; eauto.
  Qed.

  Local Hint Resolve weakening_override : core.

  Lemma weakening : forall G e t,
    has_ty G e t
    -> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
      -> has_ty G' e t.
  Proof.
    induct 1; t.
  Qed.

  Local Hint Resolve weakening : core.

  Lemma has_ty_change : forall G e t,
    has_ty G e t
    -> forall G', G' = G
      -> has_ty G' e t.
  Proof.
    t.
  Qed.

  Local Hint Resolve has_ty_change : core.

  Lemma substitution : forall G x t' e t e',
    has_ty (G $+ (x, t')) e t
    -> has_ty $0 e' t'
    -> has_ty G (subst e' x e) t.
  Proof.
    induct 1; t.
  Qed.

  Local Hint Resolve substitution : core.

  Lemma preservation0 : forall e1 e2,
    step0 e1 e2
    -> forall t, has_ty $0 e1 t
      -> has_ty $0 e2 t.
  Proof.
    invert 1; t.
  Qed.

  Local Hint Resolve preservation0 : core.

  Lemma preservation' : forall C e1 e1',
      plug C e1 e1'
      -> forall e2 e2' t, plug C e2 e2'
      -> step0 e1 e2
      -> has_ty $0 e1' t
      -> has_ty $0 e2' t.
  Proof.
    induct 1; t.
  Qed.

  Local Hint Resolve preservation' : core.
  
  Lemma preservation : forall e1 e2,
    step e1 e2
    -> forall t, has_ty $0 e1 t
      -> has_ty $0 e2 t.
  Proof.
    invert 1; t.
  Qed.

  Local Hint Resolve progress preservation : core.

  Theorem safety : forall e t, has_ty $0 e t
    -> invariantFor (trsys_of e)
                    (fun e' => value e'
                               \/ exists e'', step e' e'').
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun e' => has_ty $0 e' t); eauto.
    apply invariant_induction; simplify; eauto; equality.
  Qed.

  (* It may not be obvious that this way of defining the semantics gives us a
   * unique evaluation sequence for every well-typed program.  Let's prove
   * it. *)

  Lemma plug_not_value : forall C e v,
      value v
      -> plug C e v
      -> C = Hole /\ e = v.
  Proof.
    invert 1; invert 1; auto.
  Qed.

  Lemma step0_value : forall v e,
      value v
      -> step0 v e
      -> False.
  Proof.
    invert 1; invert 1.
  Qed.
  
  Lemma plug_det : forall C e1 e2 e1' f1 f1',
      step0 e1 e1'
      -> step0 f1 f1'
      -> plug C e1 e2
      -> forall C', plug C' f1 e2
      -> C = C' /\ e1 = f1.
  Proof.
    induct 3; invert 1;
      repeat match goal with
             | [ H : step0 _ _ |- _ ] => invert1 H
             | [ H : plug _ _ _ |- _ ] => eapply plug_not_value in H; [ | solve [ eauto ] ];
                                            propositional; subst
             | [ IH : step0 _ _ -> _, H : plug _ _ _ |- _ ] => eapply IH in H; [ | solve [ auto ] ];
                                                                 equality
             | [ _ : value ?v, _ : step0 ?v _ |- _ ] => exfalso; eapply step0_value; eauto
             end; equality.
  Qed.

  Lemma step0_det : forall e e', step0 e e'
                                 -> forall e'', step0 e e''
                                                -> e' = e''.
  Proof.
    invert 1; invert 1; auto.
  Qed.
  
  Lemma plug_func : forall C e e1,
      plug C e e1
      -> forall e2, plug C e e2
                    -> e1 = e2.
  Proof.
    induct 1; invert 1; auto; f_equal; auto.
  Qed.

  Theorem deterministic : forall e e', step e e'
                                       -> forall e'', step e e''
                                                      -> e' = e''.
  Proof.
    invert 1; invert 1.

    assert (C = C0 /\ e1 = e0) by (eapply plug_det; eassumption).
    propositional; subst.
    assert (e2 = e3) by (eapply step0_det; eassumption).
    subst.
    eapply plug_func; eassumption.
  Qed.    
End Stlc.

(** * Pairs *)

Module StlcPairs.
  Inductive exp : Set :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)

  | Pair (e1 e2 : exp)
  | Fst (e1 : exp)
  | Snd (e2 : exp).

  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1)
  (* A pair of values is a value.  (Now this relation finally becomes
   * recursive.) *)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (Pair v1 v2).

  Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
    match e2 with
      | Var y => if y ==v x then e1 else Var y
      | Const n => Const n
      | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
      | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
      | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
      (* Some bureaucratic work here to add predictable cases *)
      | Pair e2' e2'' => Pair (subst e1 x e2') (subst e1 x e2'')
      | Fst e2' => Fst (subst e1 x e2')
      | Snd e2' => Snd (subst e1 x e2')
    end.

  Inductive context : Set :=
  | Hole : context
  | Plus1 : context -> exp -> context
  | Plus2 : exp -> context -> context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context
  (* Two new context kinds, indicating left-to-right evaluation order for
   * pairs *)
  | Pair1 : context -> exp -> context
  | Pair2 : exp -> context -> context
  (* And similar for projections *)
  | Fst1 : context -> context
  | Snd1 : context -> context.
                                
  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugPlus1 : forall e e' C e2,
    plug C e e'
    -> plug (Plus1 C e2) e (Plus e' e2)
  | PlugPlus2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Plus2 v1 C) e (Plus v1 e')
  | PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')

  (* Our new plugging rules *)
  | PlugPair1 : forall e e' C e2,
    plug C e e'
    -> plug (Pair1 C e2) e (Pair e' e2)
  | PlugPair2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Pair2 v1 C) e (Pair v1 e')
  | PlugFst1 : forall e e' C,
    plug C e e'
    -> plug (Fst1 C) e (Fst e')
  | PlugSnd1 : forall e e' C,
    plug C e e'
    -> plug (Snd1 C) e (Snd e').

  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
      step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2))

  (* Reducing projections *)
  | FstPair : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Fst (Pair v1 v2)) v1
  | SndPair : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Snd (Pair v1 v2)) v2.

  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

  Definition trsys_of (e : exp) := {|
    Initial := {e};
    Step := step
  |}.


  Inductive type :=
  | Nat
  | Fun (dom ran : type)
  | Prod (t1 t2 : type) (* "Prod" for "product," as in Cartesian product *).

  Inductive has_ty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
    G $? x = Some t
    -> has_ty G (Var x) t
  | HtConst : forall G n,
    has_ty G (Const n) Nat
  | HtPlus : forall G e1 e2,
    has_ty G e1 Nat
    -> has_ty G e2 Nat
    -> has_ty G (Plus e1 e2) Nat
  | HtAbs : forall G x e1 t1 t2,
    has_ty (G $+ (x, t1)) e1 t2
    -> has_ty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
    has_ty G e1 (Fun t1 t2)
    -> has_ty G e2 t1
    -> has_ty G (App e1 e2) t2
  | HtPair : forall G e1 e2 t1 t2,
    has_ty G e1 t1
    -> has_ty G e2 t2
    -> has_ty G (Pair e1 e2) (Prod t1 t2)
  | HtFst : forall G e1 t1 t2,
    has_ty G e1 (Prod t1 t2)
    -> has_ty G (Fst e1) t1
  | HtSnd : forall G e1 t1 t2,
    has_ty G e1 (Prod t1 t2)
    -> has_ty G (Snd e1) t2.

  (* Let's copy and paste the type-soundness proof from above and adapt it. *)
End StlcPairs.

(** * Variants *)

Print sum.

Module StlcSums.
  Inductive exp : Set :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)
  | Pair (e1 e2 : exp)
  | Fst (e1 : exp)
  | Snd (e2 : exp)

  (* New cases: *)
  | Inl (e1 : exp)
  | Inr (e2 : exp)
  | Match (e' : exp) (x1 : var) (e1 : exp) (x2 : var) (e2 : exp).
  (* The last one roughly means "match e' with inl x1 => e1 | inr x2 => e2". *)

  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (Pair v1 v2)
  | VInl : forall v, value v -> value (Inl v)
  | VInr : forall v, value v -> value (Inr v).

  Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
    match e2 with
      | Var y => if y ==v x then e1 else Var y
      | Const n => Const n
      | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
      | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
      | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
      | Pair e2' e2'' => Pair (subst e1 x e2') (subst e1 x e2'')
      | Fst e2' => Fst (subst e1 x e2')
      | Snd e2' => Snd (subst e1 x e2')
      (* Some bureaucratic work here to add predictable cases *)
      | Inl e2' => Inl (subst e1 x e2')
      | Inr e2' => Inr (subst e1 x e2')
      | Match e2' x1 e21 x2 e22 => Match (subst e1 x e2')
                                         x1 (if x1 ==v x then e21 else subst e1 x e21)
                                         x2 (if x2 ==v x then e22 else subst e1 x e22)
    end.

  Inductive context : Set :=
  | Hole : context
  | Plus1 : context -> exp -> context
  | Plus2 : exp -> context -> context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context
  | Pair1 : context -> exp -> context
  | Pair2 : exp -> context -> context
  | Fst1 : context -> context
  | Snd1 : context -> context

  (* New cases: *)
  | Inl1 : context -> context
  | Inr1 : context -> context
  | Match1 : context -> var -> exp -> var -> exp -> context.
                        
  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugPlus1 : forall e e' C e2,
    plug C e e'
    -> plug (Plus1 C e2) e (Plus e' e2)
  | PlugPlus2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Plus2 v1 C) e (Plus v1 e')
  | PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')
  | PlugPair1 : forall e e' C e2,
    plug C e e'
    -> plug (Pair1 C e2) e (Pair e' e2)
  | PlugPair2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Pair2 v1 C) e (Pair v1 e')
  | PlugFst1 : forall e e' C,
    plug C e e'
    -> plug (Fst1 C) e (Fst e')
  | PlugSnd1 : forall e e' C,
    plug C e e'
    -> plug (Snd1 C) e (Snd e')

  (* Our new plugging rules *)            
  | PlugInl1 : forall e e' C,
    plug C e e'
    -> plug (Inl1 C) e (Inl e')
  | PlugInr1 : forall e e' C,
    plug C e e'
    -> plug (Inr1 C) e (Inr e')
  | PluMatch1 : forall e e' C x1 e1 x2 e2,
    plug C e e'
    -> plug (Match1 C x1 e1 x2 e2) e (Match e' x1 e1 x2 e2).

  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
      step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2))
  | FstPair : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Fst (Pair v1 v2)) v1
  | SndPair : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Snd (Pair v1 v2)) v2

  (* Reducing a [Match] *)
  | MatchInl : forall v x1 e1 x2 e2,
      value v
      -> step0 (Match (Inl v) x1 e1 x2 e2) (subst v x1 e1)
  | MatchInr : forall v x1 e1 x2 e2,
      value v
      -> step0 (Match (Inr v) x1 e1 x2 e2) (subst v x2 e2).

  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

  Definition trsys_of (e : exp) := {|
    Initial := {e};
    Step := step
  |}.


  Inductive type :=
  | Nat
  | Fun (dom ran : type)
  | Prod (t1 t2 : type)
  (* New case: *)
  | Sum (t1 t2 : type).

  Inductive has_ty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
    G $? x = Some t
    -> has_ty G (Var x) t
  | HtConst : forall G n,
    has_ty G (Const n) Nat
  | HtPlus : forall G e1 e2,
    has_ty G e1 Nat
    -> has_ty G e2 Nat
    -> has_ty G (Plus e1 e2) Nat
  | HtAbs : forall G x e1 t1 t2,
    has_ty (G $+ (x, t1)) e1 t2
    -> has_ty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
    has_ty G e1 (Fun t1 t2)
    -> has_ty G e2 t1
    -> has_ty G (App e1 e2) t2
  | HtPair : forall G e1 e2 t1 t2,
    has_ty G e1 t1
    -> has_ty G e2 t2
    -> has_ty G (Pair e1 e2) (Prod t1 t2)
  | HtFst : forall G e1 t1 t2,
    has_ty G e1 (Prod t1 t2)
    -> has_ty G (Fst e1) t1
  | HtSnd : forall G e1 t1 t2,
    has_ty G e1 (Prod t1 t2)
    -> has_ty G (Snd e1) t2

  (* New cases: *)
  | HtInl : forall G e1 t1 t2,
      has_ty G e1 t1
      -> has_ty G (Inl e1) (Sum t1 t2)
  | HtInr : forall G e1 t1 t2,
      has_ty G e1 t2
      -> has_ty G (Inr e1) (Sum t1 t2)
  | HtMatch : forall G e t1 t2 x1 e1 x2 e2 t,
      has_ty G e (Sum t1 t2)
      -> has_ty (G $+ (x1, t1)) e1 t
      -> has_ty (G $+ (x2, t2)) e2 t
      -> has_ty G (Match e x1 e1 x2 e2) t.

  (* Type-soundness proof here *)
End StlcSums.

(** * Exceptions *)

Module StlcExceptions.
  Inductive exp : Set :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)
  | Pair (e1 e2 : exp)
  | Fst (e1 : exp)
  | Snd (e2 : exp)
  | Inl (e1 : exp)
  | Inr (e2 : exp)
  | Match (e' : exp) (x1 : var) (e1 : exp) (x2 : var) (e2 : exp)

  | Throw (e1 : exp)
  | Catch (e1 : exp) (x : var) (e2 : exp).
  (* The last one roughly means "try e1 catch x => e2". *)

  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (Pair v1 v2)
  | VInl : forall v, value v -> value (Inl v)
  | VInr : forall v, value v -> value (Inr v).

  Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
    match e2 with
      | Var y => if y ==v x then e1 else Var y
      | Const n => Const n
      | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
      | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
      | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
      | Pair e2' e2'' => Pair (subst e1 x e2') (subst e1 x e2'')
      | Fst e2' => Fst (subst e1 x e2')
      | Snd e2' => Snd (subst e1 x e2')
      | Inl e2' => Inl (subst e1 x e2')
      | Inr e2' => Inr (subst e1 x e2')
      | Match e2' x1 e21 x2 e22 => Match (subst e1 x e2')
                                         x1 (if x1 ==v x then e21 else subst e1 x e21)
                                         x2 (if x2 ==v x then e22 else subst e1 x e22)

      (* New cases: *)
      | Throw e2' => Throw (subst e1 x e2')
      | Catch e2' x1 e2'' => Catch (subst e1 x e2')
                                   x1 (if x1 ==v x then e2'' else subst e1 x e2'')
    end.

  Inductive context : Set :=
  | Hole : context
  | Plus1 : context -> exp -> context
  | Plus2 : exp -> context -> context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context
  | Pair1 : context -> exp -> context
  | Pair2 : exp -> context -> context
  | Fst1 : context -> context
  | Snd1 : context -> context
  | Inl1 : context -> context
  | Inr1 : context -> context
  | Match1 : context -> var -> exp -> var -> exp -> context

  (* New cases: *)
  | Throw1 : context -> context
  | Catch1 : context -> var -> exp -> context.

  (* We modify [plug] with a new Boolean argument, to control whether [Catch1]
   * context kinds are allowed. *)
  Inductive plug : bool -> context -> exp -> exp -> Prop :=
  | PlugHole : forall ac e, plug ac Hole e e
  | PlugPlus1 : forall ac e e' C e2,
    plug ac C e e'
    -> plug ac (Plus1 C e2) e (Plus e' e2)
  | PlugPlus2 : forall ac e e' v1 C,
    value v1
    -> plug ac C e e'
    -> plug ac (Plus2 v1 C) e (Plus v1 e')
  | PlugApp1 : forall ac e e' C e2,
    plug ac C e e'
    -> plug ac (App1 C e2) e (App e' e2)
  | PlugApp2 : forall ac e e' v1 C,
    value v1
    -> plug ac C e e'
    -> plug ac (App2 v1 C) e (App v1 e')
  | PlugPair1 : forall ac e e' C e2,
    plug ac C e e'
    -> plug ac (Pair1 C e2) e (Pair e' e2)
  | PlugPair2 : forall ac e e' v1 C,
    value v1
    -> plug ac C e e'
    -> plug ac (Pair2 v1 C) e (Pair v1 e')
  | PlugFst1 : forall ac e e' C,
    plug ac C e e'
    -> plug ac (Fst1 C) e (Fst e')
  | PlugSnd1 : forall ac e e' C,
    plug ac C e e'
    -> plug ac (Snd1 C) e (Snd e')
  | PlugInl1 : forall ac e e' C,
    plug ac C e e'
    -> plug ac (Inl1 C) e (Inl e')
  | PlugInr1 : forall ac e e' C,
    plug ac C e e'
    -> plug ac (Inr1 C) e (Inr e')
  | PluMatch1 : forall ac e e' C x1 e1 x2 e2,
    plug ac C e e'
    -> plug ac (Match1 C x1 e1 x2 e2) e (Match e' x1 e1 x2 e2)
  | PlugThrow1 : forall ac e e' C,
    plug ac C e e'
    -> plug ac (Throw1 C) e (Throw e')
  | PlugCatch1 : forall e e' C x1 e1,
    plug true C e e'
    -> plug true (Catch1 C x1 e1) e (Catch e' x1 e1).

  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
      step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2))
  | FstPair : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Fst (Pair v1 v2)) v1
  | SndPair : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Snd (Pair v1 v2)) v2
  | MatchInl : forall v x1 e1 x2 e2,
      value v
      -> step0 (Match (Inl v) x1 e1 x2 e2) (subst v x1 e1)
  | MatchInr : forall v x1 e1 x2 e2,
      value v
      -> step0 (Match (Inr v) x1 e1 x2 e2) (subst v x2 e2)

  | ThrowBubble : forall v C e,
      plug false C (Throw v) e
      -> value v
      -> C <> Hole
      -> step0 e (Throw v)
  | CatchValue : forall v x1 e1,
      value v
      -> step0 (Catch v x1 e1) v
  | CatchThrow : forall v x1 e1,
      value v
      -> step0 (Catch (Throw v) x1 e1) (subst v x1 e1).

  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
    plug true C e1 e1'
    -> plug true C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

  Definition trsys_of (e : exp) := {|
    Initial := {e};
    Step := step
  |}.


  Inductive type :=
  | Nat
  | Fun (dom ran : type)
  | Prod (t1 t2 : type)
  | Sum (t1 t2 : type).

  Inductive has_ty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
    G $? x = Some t
    -> has_ty G (Var x) t
  | HtConst : forall G n,
    has_ty G (Const n) Nat
  | HtPlus : forall G e1 e2,
    has_ty G e1 Nat
    -> has_ty G e2 Nat
    -> has_ty G (Plus e1 e2) Nat
  | HtAbs : forall G x e1 t1 t2,
    has_ty (G $+ (x, t1)) e1 t2
    -> has_ty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
    has_ty G e1 (Fun t1 t2)
    -> has_ty G e2 t1
    -> has_ty G (App e1 e2) t2
  | HtPair : forall G e1 e2 t1 t2,
    has_ty G e1 t1
    -> has_ty G e2 t2
    -> has_ty G (Pair e1 e2) (Prod t1 t2)
  | HtFst : forall G e1 t1 t2,
    has_ty G e1 (Prod t1 t2)
    -> has_ty G (Fst e1) t1
  | HtSnd : forall G e1 t1 t2,
    has_ty G e1 (Prod t1 t2)
    -> has_ty G (Snd e1) t2
  | HtInl : forall G e1 t1 t2,
      has_ty G e1 t1
      -> has_ty G (Inl e1) (Sum t1 t2)
  | HtInr : forall G e1 t1 t2,
      has_ty G e1 t2
      -> has_ty G (Inr e1) (Sum t1 t2)
  | HtMatch : forall G e t1 t2 x1 e1 x2 e2 t,
      has_ty G e (Sum t1 t2)
      -> has_ty (G $+ (x1, t1)) e1 t
      -> has_ty (G $+ (x2, t2)) e2 t
      -> has_ty G (Match e x1 e1 x2 e2) t

  (* New cases: *)
  | HtThrow : forall G e1 t,
      has_ty G e1 Nat
      -> has_ty G (Throw e1) t
  | HtCatch : forall G e x1 e1 t,
      has_ty G e t
      -> has_ty (G $+ (x1, Nat)) e1 t
      -> has_ty G (Catch e x1 e1) t.
End StlcExceptions.

(** * Mutable Variables *)

Module StlcMutable.
  Inductive exp : Set :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)
  | Pair (e1 e2 : exp)
  | Fst (e1 : exp)
  | Snd (e2 : exp)
  | Inl (e1 : exp)
  | Inr (e2 : exp)
  | Match (e' : exp) (x1 : var) (e1 : exp) (x2 : var) (e2 : exp)

  (* New cases: *)
  | GetVar (x : var)
  | SetVar (x : var) (e : exp).
  (* Note that we are distinguishing between mutable and immutable variables,
   * keeping the latter to bind in [Abs] and [Match]. *)

  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (Pair v1 v2)
  | VInl : forall v, value v -> value (Inl v)
  | VInr : forall v, value v -> value (Inr v).

  Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
    match e2 with
      | Var y => if y ==v x then e1 else Var y
      | Const n => Const n
      | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
      | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
      | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
      | Pair e2' e2'' => Pair (subst e1 x e2') (subst e1 x e2'')
      | Fst e2' => Fst (subst e1 x e2')
      | Snd e2' => Snd (subst e1 x e2')
      | Inl e2' => Inl (subst e1 x e2')
      | Inr e2' => Inr (subst e1 x e2')
      | Match e2' x1 e21 x2 e22 => Match (subst e1 x e2')
                                         x1 (if x1 ==v x then e21 else subst e1 x e21)
                                         x2 (if x2 ==v x then e22 else subst e1 x e22)
      | GetVar y => GetVar y
      | SetVar y e2' => SetVar y (subst e1 x e2')
    end.

  Inductive context : Set :=
  | Hole : context
  | Plus1 : context -> exp -> context
  | Plus2 : exp -> context -> context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context
  | Pair1 : context -> exp -> context
  | Pair2 : exp -> context -> context
  | Fst1 : context -> context
  | Snd1 : context -> context
  | Inl1 : context -> context
  | Inr1 : context -> context
  | Match1 : context -> var -> exp -> var -> exp -> context
  (* New case: *)
  | SetVar1 : var -> context -> context.
                        
  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugPlus1 : forall e e' C e2,
    plug C e e'
    -> plug (Plus1 C e2) e (Plus e' e2)
  | PlugPlus2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Plus2 v1 C) e (Plus v1 e')
  | PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')
  | PlugPair1 : forall e e' C e2,
    plug C e e'
    -> plug (Pair1 C e2) e (Pair e' e2)
  | PlugPair2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Pair2 v1 C) e (Pair v1 e')
  | PlugFst1 : forall e e' C,
    plug C e e'
    -> plug (Fst1 C) e (Fst e')
  | PlugSnd1 : forall e e' C,
    plug C e e'
    -> plug (Snd1 C) e (Snd e')
  | PlugInl1 : forall e e' C,
    plug C e e'
    -> plug (Inl1 C) e (Inl e')
  | PlugInr1 : forall e e' C,
    plug C e e'
    -> plug (Inr1 C) e (Inr e')
  | PluMatch1 : forall e e' C x1 e1 x2 e2,
    plug C e e'
    -> plug (Match1 C x1 e1 x2 e2) e (Match e' x1 e1 x2 e2)
  
   (* Our new plugging rules *)            
  | PluSetVar1 : forall x e e' C,
      plug C e e'
      -> plug (SetVar1 x C) e (SetVar x e').

  Definition valuation := fmap var exp.

  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
      step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2))
  | FstPair : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Fst (Pair v1 v2)) v1
  | SndPair : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Snd (Pair v1 v2)) v2
  | MatchInl : forall v x1 e1 x2 e2,
      value v
      -> step0 (Match (Inl v) x1 e1 x2 e2) (subst v x1 e1)
  | MatchInr : forall v x1 e1 x2 e2,
      value v
      -> step0 (Match (Inr v) x1 e1 x2 e2) (subst v x2 e2).

  (* We build an intermediate relation on top of [step0], allowing for
   * consultation of the mutable-variable valuation. *)
  Inductive step1 : valuation * exp -> valuation * exp -> Prop :=
  | Lift : forall env e1 e2,
    step0 e1 e2
    -> step1 (env, e1) (env, e2)
  | Read : forall env x v,
      env $? x = Some v
      -> step1 (env, GetVar x) (env, v)
  | Overwrite : forall env x v,
      value v
      -> step1 (env, SetVar x v) (env $+ (x, v), v).
  
  Inductive step : valuation * exp -> valuation * exp -> Prop :=
  | StepRule : forall C env1 e1 env2 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step1 (env1, e1) (env2, e2)
    -> step (env1, e1') (env2, e2').

  Definition trsys_of (env : valuation) (e : exp) := {|
    Initial := {(env, e)};
    Step := step
  |}.


  Inductive type :=
  | Nat
  | Fun (dom ran : type)
  | Prod (t1 t2 : type)
  | Sum (t1 t2 : type).

  (* Now there will be two typing contexts, one for mutable variables and one
   * for immutable. *)
  Inductive has_ty (M : fmap var type) : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
    G $? x = Some t
    -> has_ty M G (Var x) t
  | HtConst : forall G n,
    has_ty M G (Const n) Nat
  | HtPlus : forall G e1 e2,
    has_ty M G e1 Nat
    -> has_ty M G e2 Nat
    -> has_ty M G (Plus e1 e2) Nat
  | HtAbs : forall G x e1 t1 t2,
    has_ty M (G $+ (x, t1)) e1 t2
    -> has_ty M G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
    has_ty M G e1 (Fun t1 t2)
    -> has_ty M G e2 t1
    -> has_ty M G (App e1 e2) t2
  | HtPair : forall G e1 e2 t1 t2,
    has_ty M G e1 t1
    -> has_ty M G e2 t2
    -> has_ty M G (Pair e1 e2) (Prod t1 t2)
  | HtFst : forall G e1 t1 t2,
    has_ty M G e1 (Prod t1 t2)
    -> has_ty M G (Fst e1) t1
  | HtSnd : forall G e1 t1 t2,
    has_ty M G e1 (Prod t1 t2)
    -> has_ty M G (Snd e1) t2
  | HtInl : forall G e1 t1 t2,
      has_ty M G e1 t1
      -> has_ty M G (Inl e1) (Sum t1 t2)
  | HtInr : forall G e1 t1 t2,
      has_ty M G e1 t2
      -> has_ty M G (Inr e1) (Sum t1 t2)
  | HtMatch : forall G e t1 t2 x1 e1 x2 e2 t,
      has_ty M G e (Sum t1 t2)
      -> has_ty M (G $+ (x1, t1)) e1 t
      -> has_ty M (G $+ (x2, t2)) e2 t
      -> has_ty M G (Match e x1 e1 x2 e2) t

  (* New cases: *)
  | HtGetVar : forall G x t,
      M $? x = Some t
      -> has_ty M G (GetVar x) t
  | HtSetVar : forall G x e t,
      M $? x = Some t
      -> has_ty M G e t
      -> has_ty M G (SetVar x e) t.
End StlcMutable.

(** * Concurrency *)

Module StlcConcur.
  Inductive exp : Set :=
  | Var (x : var)
  | Const (n : nat)
  | Plus (e1 e2 : exp)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)
  | Pair (e1 e2 : exp)
  | Fst (e1 : exp)
  | Snd (e2 : exp)
  | Inl (e1 : exp)
  | Inr (e2 : exp)
  | Match (e' : exp) (x1 : var) (e1 : exp) (x2 : var) (e2 : exp)
  | GetVar (x : var)
  | SetVar (x : var) (e : exp)

  (* New cases: *)
  | Par (e1 e2 : exp).           
  (* This form evaluates both expressions and forms a pair of their
   * results, if they terminate. *)

  Inductive value : exp -> Prop :=
  | VConst : forall n, value (Const n)
  | VAbs : forall x e1, value (Abs x e1)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (Pair v1 v2)
  | VInl : forall v, value v -> value (Inl v)
  | VInr : forall v, value v -> value (Inr v).

  Fixpoint subst (e1 : exp) (x : string) (e2 : exp) : exp :=
    match e2 with
      | Var y => if y ==v x then e1 else Var y
      | Const n => Const n
      | Plus e2' e2'' => Plus (subst e1 x e2') (subst e1 x e2'')
      | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
      | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
      | Pair e2' e2'' => Pair (subst e1 x e2') (subst e1 x e2'')
      | Fst e2' => Fst (subst e1 x e2')
      | Snd e2' => Snd (subst e1 x e2')
      | Inl e2' => Inl (subst e1 x e2')
      | Inr e2' => Inr (subst e1 x e2')
      | Match e2' x1 e21 x2 e22 => Match (subst e1 x e2')
                                         x1 (if x1 ==v x then e21 else subst e1 x e21)
                                         x2 (if x2 ==v x then e22 else subst e1 x e22)
      | GetVar y => GetVar y
      | SetVar y e2' => SetVar y (subst e1 x e2')
      | Par e2' e2'' => Par (subst e1 x e2') (subst e1 x e2'')
    end.

  Inductive context : Set :=
  | Hole : context
  | Plus1 : context -> exp -> context
  | Plus2 : exp -> context -> context
  | App1 : context -> exp -> context
  | App2 : exp -> context -> context
  | Pair1 : context -> exp -> context
  | Pair2 : exp -> context -> context
  | Fst1 : context -> context
  | Snd1 : context -> context
  | Inl1 : context -> context
  | Inr1 : context -> context
  | Match1 : context -> var -> exp -> var -> exp -> context
  | SetVar1 : var -> context -> context

  (* New cases: *)
  | Par1 : context -> exp -> context
  | Par2 : exp -> context -> context.
                                  
  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugPlus1 : forall e e' C e2,
    plug C e e'
    -> plug (Plus1 C e2) e (Plus e' e2)
  | PlugPlus2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Plus2 v1 C) e (Plus v1 e')
  | PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')
  | PlugPair1 : forall e e' C e2,
    plug C e e'
    -> plug (Pair1 C e2) e (Pair e' e2)
  | PlugPair2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (Pair2 v1 C) e (Pair v1 e')
  | PlugFst1 : forall e e' C,
    plug C e e'
    -> plug (Fst1 C) e (Fst e')
  | PlugSnd1 : forall e e' C,
    plug C e e'
    -> plug (Snd1 C) e (Snd e')
  | PlugInl1 : forall e e' C,
    plug C e e'
    -> plug (Inl1 C) e (Inl e')
  | PlugInr1 : forall e e' C,
    plug C e e'
    -> plug (Inr1 C) e (Inr e')
  | PluMatch1 : forall e e' C x1 e1 x2 e2,
    plug C e e'
    -> plug (Match1 C x1 e1 x2 e2) e (Match e' x1 e1 x2 e2)
  | PluSetVar1 : forall x e e' C,
      plug C e e'
      -> plug (SetVar1 x C) e (SetVar x e')

  (* Our new plugging rules: *)
  | PlugPar1 : forall e e' C e2,
    plug C e e'
    -> plug (Par1 C e2) e (Par e' e2)
  | PlugPar2 : forall e e' e1 C,
    plug C e e'
    -> plug (Par2 e1 C) e (Par e1 e').

  Definition valuation := fmap var exp.
  
  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)
  | Add : forall n1 n2,
      step0 (Plus (Const n1) (Const n2)) (Const (n1 + n2))
  | FstPair : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Fst (Pair v1 v2)) v1
  | SndPair : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Snd (Pair v1 v2)) v2
  | MatchInl : forall v x1 e1 x2 e2,
      value v
      -> step0 (Match (Inl v) x1 e1 x2 e2) (subst v x1 e1)
  | MatchInr : forall v x1 e1 x2 e2,
      value v
      -> step0 (Match (Inr v) x1 e1 x2 e2) (subst v x2 e2)

  (* New case: *)
  | ParDone : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Par v1 v2) (Pair v1 v2).

  Inductive step1 : valuation * exp -> valuation * exp -> Prop :=
  | Lift : forall env e1 e2,
    step0 e1 e2
    -> step1 (env, e1) (env, e2)
  | Read : forall env x v,
      env $? x = Some v
      -> step1 (env, GetVar x) (env, v)
  | Overwrite : forall env x v,
      value v
      -> step1 (env, SetVar x v) (env $+ (x, v), v).
               
  Inductive step : valuation * exp -> valuation * exp -> Prop :=
  | StepRule : forall C env1 e1 env2 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step1 (env1, e1) (env2, e2)
    -> step (env1, e1') (env2, e2').

  Definition trsys_of (env : valuation) (e : exp) := {|
    Initial := {(env, e)};
    Step := step
  |}.


  Inductive type :=
  | Nat
  | Fun (dom ran : type)
  | Prod (t1 t2 : type)
  | Sum (t1 t2 : type).

  Inductive has_ty (M : fmap var type) : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
    G $? x = Some t
    -> has_ty M G (Var x) t
  | HtConst : forall G n,
    has_ty M G (Const n) Nat
  | HtPlus : forall G e1 e2,
    has_ty M G e1 Nat
    -> has_ty M G e2 Nat
    -> has_ty M G (Plus e1 e2) Nat
  | HtAbs : forall G x e1 t1 t2,
    has_ty M (G $+ (x, t1)) e1 t2
    -> has_ty M G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
    has_ty M G e1 (Fun t1 t2)
    -> has_ty M G e2 t1
    -> has_ty M G (App e1 e2) t2
  | HtPair : forall G e1 e2 t1 t2,
    has_ty M G e1 t1
    -> has_ty M G e2 t2
    -> has_ty M G (Pair e1 e2) (Prod t1 t2)
  | HtFst : forall G e1 t1 t2,
    has_ty M G e1 (Prod t1 t2)
    -> has_ty M G (Fst e1) t1
  | HtSnd : forall G e1 t1 t2,
    has_ty M G e1 (Prod t1 t2)
    -> has_ty M G (Snd e1) t2
  | HtInl : forall G e1 t1 t2,
      has_ty M G e1 t1
      -> has_ty M G (Inl e1) (Sum t1 t2)
  | HtInr : forall G e1 t1 t2,
      has_ty M G e1 t2
      -> has_ty M G (Inr e1) (Sum t1 t2)
  | HtMatch : forall G e t1 t2 x1 e1 x2 e2 t,
      has_ty M G e (Sum t1 t2)
      -> has_ty M (G $+ (x1, t1)) e1 t
      -> has_ty M (G $+ (x2, t2)) e2 t
      -> has_ty M G (Match e x1 e1 x2 e2) t
  | HtGetVar : forall G x t,
      M $? x = Some t
      -> has_ty M G (GetVar x) t
  | HtSetVar : forall G x e t,
      M $? x = Some t
      -> has_ty M G e t
      -> has_ty M G (SetVar x e) t

  (* New cases: *)
  | HtPar : forall G e1 t1 e2 t2,
      has_ty M G e1 t1
      -> has_ty M G e2 t2
      -> has_ty M G (Par e1 e2) (Prod t1 t2).

  (* Type-soundness proof *)
End StlcConcur.
