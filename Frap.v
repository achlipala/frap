Require Import String Arith Omega Program Sets Relations Map Var Invariant.
Export String Arith Sets Relations Map Var Invariant.
Require Import List.
Export ListNotations.
Open Scope string_scope.

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

Ltac simplify := simpl in *; intros; try autorewrite with core in *.

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

Ltac equality := congruence.

Ltac cases E :=
  (is_var E; destruct E)
  || match type of E with
     | {_} + {_} => destruct E
     | _ => let Heq := fresh "Heq" in destruct E eqn:Heq
     end.

Global Opaque max min.
