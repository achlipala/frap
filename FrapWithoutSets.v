Require Import Eqdep String NArith Arith Lia Program Sets Relations Map Var Invariant Bool ModelCheck.
Export Ascii String Arith Sets Relations Map Var Invariant Bool ModelCheck.
Require Import List.
Export List ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Ltac inductN n :=
  match goal with
    | [ |- forall x : ?E, _ ] =>
      match type of E with
        | Prop =>
          let H := fresh in intro H;
            match n with
              | 1 => dependent induction H
              | S ?n' => inductN n'
            end
        | _ => intro; inductN n
      end
  end.

Ltac same_structure x y :=
  match x with
  | ?f ?a1 ?b1 ?c1 ?d1 =>
    match y with
    | f ?a2 ?b2 ?c2 ?d2 => same_structure a1 a2; same_structure b1 b2; same_structure c1 c2; same_structure d1 d2
    | _ => fail 2
    end
  | ?f ?a1 ?b1 ?c1 =>
    match y with
    | f ?a2 ?b2 ?c2 => same_structure a1 a2; same_structure b1 b2; same_structure c1 c2
    | _ => fail 2
    end
  | ?f ?a1 ?b1 =>
    match y with
    | f ?a2 ?b2 => same_structure a1 a2; same_structure b1 b2
    | _ => fail 2
    end
  | ?f ?a1 =>
    match y with
    | f ?a2 => same_structure a1 a2
    | _ => fail 2
    end
  | _ =>
    match y with
    | ?f ?a1 ?b1 ?c1 ?d1 =>
      match x with
      | f ?a2 ?b2 ?c2 ?d2 => same_structure a1 a2; same_structure b1 b2; same_structure c1 c2; same_structure d1 d2
      | _ => fail 2
      end
    | ?f ?a1 ?b1 ?c1 =>
      match x with
      | f ?a2 ?b2 ?c2 => same_structure a1 a2; same_structure b1 b2; same_structure c1 c2
      | _ => fail 2
      end
    | ?f ?a1 ?b1 =>
      match x with
      | f ?a2 ?b2 => same_structure a1 a2; same_structure b1 b2
      | _ => fail 2
      end
    | ?f ?a1 =>
      match x with
      | f ?a2 => same_structure a1 a2
      | _ => fail 2
      end
    | _ => idtac
    end
  end.

Ltac instantiate_obvious1 H :=
  match type of H with
  | _ ++ _ = _ ++ _ -> _ => fail 1
  | ?x = ?y -> _ =>
    (same_structure x y; specialize (H eq_refl))
    || (has_evar (x, y); fail 3)
  | JMeq.JMeq ?x ?y -> _ =>
    (same_structure x y; specialize (H JMeq.JMeq_refl))
    || (has_evar (x, y); fail 3)
  | forall x : ?T, _ =>
    match type of T with
    | Prop => fail 1
    | _ =>
      let x' := fresh x in
      evar (x' : T);
      let x'' := eval unfold x' in x' in specialize (H x''); clear x';
        instantiate_obvious1 H
    end
  end.

Ltac instantiate_obvious H :=
  match type of H with
    | context[@eq string _  _] => idtac
    | _ => repeat instantiate_obvious1 H
  end.

Ltac instantiate_obviouses :=
  repeat match goal with
         | [ H : _ |- _ ] => instantiate_obvious H
         end.

(** * Interlude: special notations and induction principle for [N] *)

(* Note: recurse is an identifier, but we will always use the name "recurse" by convention *)
(*Declare Scope N_recursion_scope.*)
Notation "recurse 'by' 'cases' | 0 => A | n + 1 => B 'end'" :=
  (N.recursion A (fun n recurse => B))
  (at level 11, A at level 200, n at level 0, B at level 200,
   format "'[hv' recurse  'by'  'cases' '//' '|'  0  =>  A '//' '|'  n  +  1  =>  B '//' 'end' ']'")
: N_recursion_scope.

Open Scope N_recursion_scope.

Lemma indN: forall (P: N -> Prop),
    P 0%N ->                                 (* base case to prove *)
    (forall n: N, P n -> P (n + 1)%N) ->     (* inductive case to prove *)
    forall n, P n.                           (* conclusion to enjoy *)
Proof. setoid_rewrite N.add_1_r. exact N.peano_ind. Qed.

Ltac induct e := (induction e using indN || inductN e || dependent induction e); instantiate_obviouses.

Ltac invert' H := inversion H; clear H; subst.

Ltac invertN n :=
  match goal with
    | [ |- forall x : ?E, _ ] =>
      match type of E with
        | Prop =>
          let H := fresh in intro H;
            match n with
              | 1 => invert' H
              | S ?n' => invertN n'
            end
        | _ => intro; invertN n
      end
  end.

Ltac invert e := invertN e || invert' e.

Ltac invert0 e := invert e; fail.
Ltac invert1 e := invert0 e || (invert e; []).
Ltac invert2 e := invert1 e || (invert e; [|]).

Ltac maps_neq :=
  match goal with
  | [ H : ?m1 = ?m2 |- _ ] =>
    let rec recur E :=
        match E with
        | ?E' $+ (?k, _) => 
          (apply (f_equal (fun m => m $? k)) in H; simpl in *; autorewrite with core in *; simpl in *; congruence)
          || recur E'
        end in
    recur m1 || recur m2
end.

Ltac fancy_neq :=
  repeat match goal with
         | _ => maps_neq
         | [ H : @eq (nat -> _) _ _ |- _ ] => apply (f_equal (fun f => f 0)) in H
         | [ H : @eq ?T _ _ |- _ ] =>
           match eval compute in T with
           | fmap _ _ => fail 1
           | _ => invert H
           end
         end.

Ltac maps_equal' := progress Frap.Map.M.maps_equal; autorewrite with core; simpl.

Ltac removeDups :=
  match goal with
  | [ |- context[constant ?ls] ] =>
    someMatch ls;
    erewrite (@removeDups_ok _ ls)
      by repeat (apply RdNil
                 || (apply RdNew; [ simpl; intuition (congruence || solve [ fancy_neq ]) | ])
                 || (apply RdDup; [ simpl; intuition (congruence || (repeat (maps_equal' || f_equal))) | ]))
  end.

Ltac doSubtract :=
  match goal with
  | [ |- context[@minus ?A (@constant ?A1 ?ls) (@constant ?A2 ?ls0)] ] =>
    match A with
    | A1 => idtac
    | _ => change (@constant A1 ls) with (@constant A ls)
    end;
    match A with
    | A2 => idtac
    | _ => change (@constant A2 ls0) with (@constant A ls0)
    end;
    erewrite (@doSubtract_ok A ls ls0)
      by repeat (apply DsNil
                 || (apply DsKeep; [ simpl; intuition (congruence || solve [ fancy_neq ]) | ])
                 || (apply DsDrop; [ simpl; intuition (congruence || (repeat (maps_equal' || f_equal))) | ]))
  end.

Ltac simpl_maps :=
  repeat match goal with
         | [ |- context[add ?m ?k1 ?v $? ?k2] ] =>
           (rewrite (@lookup_add_ne _ _ m k1 k2 v) by (congruence || lia))
           || (rewrite (@lookup_add_eq _ _ m k1 k2 v) by (congruence || lia))
         end.

Ltac simplify := repeat (unifyTails; pose proof I);
                repeat match goal with
                       | [ H : True |- _ ] => clear H
                       end;
                repeat progress (simpl in *; intros; try autorewrite with core in *; simpl_maps);
                                 repeat (normalize_set || doSubtract).
Ltac propositional := intuition idtac.

Ltac linear_arithmetic := intros;
    repeat match goal with
           | [ |- context[max ?a ?b] ] =>
             let Heq := fresh "Heq" in destruct (Max.max_spec a b) as [[? Heq] | [? Heq]];
               rewrite Heq in *; clear Heq
           | [ _ : context[max ?a ?b] |- _ ] =>
             let Heq := fresh "Heq" in destruct (Max.max_spec a b) as [[? Heq] | [? Heq]];
               rewrite Heq in *; clear Heq
           | [ |- context[min ?a ?b] ] =>
             let Heq := fresh "Heq" in destruct (Min.min_spec a b) as [[? Heq] | [? Heq]];
               rewrite Heq in *; clear Heq
           | [ _ : context[min ?a ?b] |- _ ] =>
             let Heq := fresh "Heq" in destruct (Min.min_spec a b) as [[? Heq] | [? Heq]];
               rewrite Heq in *; clear Heq
           end; lia.

Ltac equality := intuition congruence.

Ltac cases E :=
  ((repeat match type of E with
           | _ \/ _ => destruct E as [E | E]
           end)
   || (is_var E; destruct E)
   || match type of E with
      | {_} + {_} => destruct E
      | _ => let Heq := fresh "Heq" in destruct E eqn:Heq
      end);
  repeat match goal with
         | [ H : _ = left _ |- _ ] => clear H
         | [ H : _ = right _ |- _ ] => clear H
         end.

Global Opaque max min.

Infix "==n" := eq_nat_dec (no associativity, at level 50).
Infix "<=?" := le_lt_dec.

Export Frap.Map.

Ltac maps_equal := Frap.Map.M.maps_equal; simplify.

Ltac first_order := firstorder idtac.


(** * Model checking *)

Lemma eq_iff : forall P Q,
    P = Q
    -> (P <-> Q).
Proof.
  equality.
Qed.

Ltac sets0 := Sets.sets ltac:(simpl in *; intuition (subst; auto; try equality; try linear_arithmetic)).

Ltac sets := propositional;
  try match goal with
      | [ |- @eq (?T -> Prop) _ _ ] =>
        change (T -> Prop) with (set T)
      end;
  try match goal with
      | [ |- @eq (set _) _ _ ] =>
        let x := fresh "x" in
        apply sets_equal; intro x;
        repeat match goal with
               | [ H : @eq (set _) _ _ |- _ ] => apply (f_equal (fun f => f x)) in H;
                                                apply eq_iff in H
               end
      end; sets0;
  try match goal with
      | [ H : @eq (set ?T) _ _, x : ?T |- _ ] =>
        repeat match goal with
               | [ H : @eq (set T) _ _ |- _ ] => apply (f_equal (fun f => f x)) in H;
                                                 apply eq_iff in H
               end;
          solve [ sets0 ]
      end.

Ltac model_check_invert1 :=
  match goal with
  | [ H : ?P |- _ ] =>
    match type of P with
    | Prop => invert H;
              repeat match goal with
                     | [ H : existT _ ?x _ = existT _ ?x _ |- _ ] =>
                       apply inj_pair2 in H; subst
                     end; simplify
    end
  end.

Ltac model_check_invert := simplify; subst; repeat model_check_invert1.

Lemma oneStepClosure_solve : forall A (sys : trsys A) I I',
  oneStepClosure sys I I'
  -> I = I'
  -> oneStepClosure sys I I.
Proof.
  equality.
Qed.

Ltac singletoner := try (exfalso; solve [ sets ]);
  repeat match goal with
         (* | _ => apply singleton_in *)
         | [ |- _ ?S ] => idtac S; apply singleton_in
         | [ |- (_ \cup _) _ ] => apply singleton_in_other
         end.

Ltac closure :=
  repeat (apply oneStepClosure_empty
          || (apply oneStepClosure_split; [ model_check_invert; try equality; solve [ singletoner ] | ])).

Ltac model_check_done := apply MscDone.
Ltac model_check_step := eapply MscStep; [ closure | simplify ].

Ltac model_check_steps1 := model_check_step || model_check_done.
Ltac model_check_steps := repeat model_check_steps1.

Ltac model_check_finish := simplify; propositional; subst; simplify; try equality; try linear_arithmetic.

Ltac model_check_infer :=
  apply multiStepClosure_ok; simplify; model_check_steps.

Ltac model_check_find_invariant :=
  simplify; eapply invariant_weaken; [ model_check_infer | ]; cbv beta in *.

Ltac model_check := model_check_find_invariant; model_check_finish.

Inductive ordering (n m : nat) :=
| Lt (_ : n < m)
| Eq (_ : n = m)
| Gt (_ : n > m).

Local Hint Constructors ordering : core.
Local Hint Extern 1 (_ < _) => lia : core.
Local Hint Extern 1 (_ > _) => lia : core.

Theorem totally_ordered : forall n m, ordering n m.
Proof.
  induction n; destruct m; simpl; eauto.
  destruct (IHn m); eauto.
Qed.

Ltac total_ordering N M := destruct (totally_ordered N M).

Ltac inList x xs :=
  match xs with
  | (x, _) => true
  | (_, ?xs') => inList x xs'
  | _ => false
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
  | [ |- context[@add ?A ?B ?m ?k ?v] ] =>
    simplify_map' (m $+ (k, v)) tt ltac:(fun m' =>
                                           replace (@add A B m k v) with m' by maps_equal)
  end.

Require Import Classical.
Ltac excluded_middle P := destruct (classic P).

Lemma join_idempotent: forall (A B : Type) (m : fmap A B), (m $++ m) = m.
Proof.
  simplify; apply fmap_ext; simplify.
  cases (m $? k).
  - rewrite lookup_join1; auto.
    eauto using lookup_Some_dom.
  - rewrite lookup_join2; auto.
    eauto using lookup_None_dom.
Qed.
  
Lemma includes_refl: forall  (A B : Type) (m : fmap A B), m $<= m.
Proof.
  simplify.
  apply includes_intro; auto.
Qed.

Ltac dep_cases E :=
  let x := fresh "x" in
    remember E as x; simpl in x; dependent destruction x;
      try match goal with
            | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
          end.

(** * More with [N] *)

Lemma recursion_step: forall {A: Type} (a: A) (f: N -> A -> A) (n: N),
    N.recursion a f (n + 1)%N = f n (N.recursion a f n).
Proof.
  intros until f. setoid_rewrite N.add_1_r.
  eapply N.recursion_succ; cbv; intuition congruence.
Qed.

Ltac head f :=
  match f with
  | ?g _ => head g
  | _ => constr:(f)
  end.

(* If a function f is defined as

  recurse by cases
  | 0 => base
  | k + 1 => step recurse k
  end.

  and we have an occurrence of (f (k + 1)) in our goal, we can use
  "unfold_recurse f k" to replace (f (k + 1)) by (step (f k) k),
  ie it allows us to unfold one recursive step. *)
Ltac unfold_recurse f k :=
  let h := head f in
  let rhs := eval unfold h in f in
  lazymatch rhs with
  | N.recursion ?base ?step =>
    let g := eval cbv beta in (step k (f k)) in
    rewrite (recursion_step base step k : f (k + 1)%N = g) in *
  | _ => let expected := open_constr:(N.recursion _ _) in
         fail "The provided term" f "expands to" rhs "which is not of the expected form" expected
  end.

(* This will make "simplify" a bit less nice in some cases (but these are easily worked around using
   linear_arithmetic). *)
Arguments N.mul: simpl never.
Arguments N.add: simpl never.
