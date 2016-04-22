Require Import Eqdep String Arith Omega Program Sets Relations Map Var Invariant Bool ModelCheck.
Export String Arith Sets Relations Map Var Invariant Bool ModelCheck.
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

Ltac induct e := inductN e || dependent induction e.

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
  | [ |- context[constant ?ls \setminus constant ?ls0] ] =>
    erewrite (@doSubtract_ok _ ls ls0)
      by repeat (apply DsNil
                 || (apply DsKeep; [ simpl; intuition (congruence || solve [ fancy_neq ]) | ])
                 || (apply DsDrop; [ simpl; intuition (congruence || (repeat (maps_equal' || f_equal))) | ]))
  end.

Ltac simpl_maps :=
  repeat match goal with
         | [ |- context[add ?m ?k1 ?v $? ?k2] ] =>
           (rewrite (@lookup_add_ne _ _ m k1 k2 v) by (congruence || omega))
           || (rewrite (@lookup_add_eq _ _ m k1 k2 v) by (congruence || omega))
         end.

Ltac simplify := repeat (unifyTails; pose proof I);
                repeat match goal with
                       | [ H : True |- _ ] => clear H
                       end;
                repeat progress (simpl in *; intros; try autorewrite with core in *; simpl_maps);
                                 repeat (removeDups || doSubtract).
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
           end; omega.

Ltac equality := intuition congruence.

Ltac cases E :=
  ((is_var E; destruct E)
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

Ltac sets := Sets.sets ltac:(simpl in *; intuition (subst; auto)).

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

Ltac model_check_done :=
  apply MscDone; eapply oneStepClosure_solve; [ closure | simplify; solve [ sets ] ].

Ltac model_check_step :=
  eapply MscStep; [ closure | simplify ].

Ltac model_check_steps1 := model_check_done || model_check_step.
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

Local Hint Constructors ordering.
Local Hint Extern 1 (_ < _) => omega.
Local Hint Extern 1 (_ > _) => omega.

Theorem totally_ordered : forall n m, ordering n m.
Proof.
  induction n; destruct m; simpl; eauto.
  destruct (IHn m); eauto.
Qed.

Ltac total_ordering N M := destruct (totally_ordered N M).

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
  | [ |- context[@add ?A ?B ?m ?k ?v] ] =>
    simplify_map' (m $+ (k, v)) tt ltac:(fun m' =>
                                           replace (@add A B m k v) with m' by maps_equal)
  end.
