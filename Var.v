Require Import String.


Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.

Infix "==v" := var_eq (no associativity, at level 50).
