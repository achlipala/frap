(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Supplementary Coq material: polymorphism and generic data structures
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.
(* This command sets up automatic inference of tedious arguments. *)

(* One of the recurring ingredients in effective machine formalization is data
 * structures, and, as in general programming, we want to be able to define data
 * structures that are *generic* in the kinds of data they contain.  Coq
 * supports such things in roughly the same way as Haskell and OCaml, via
 * *parametric polymorphism*, which is closely related to the idea of *generics*
 * in languages like Java. *)

(* Our first example: the [option] type family.  While Java and friends force
 * all sorts of different types to include the special value [null], in Coq we
 * request that option explicitly by wrapping a type in [option].  Specifically,
 * any value of type [option A], for some type [A], is either [None] (sort of
 * like [null]) or [Some v] for a [v] of type [A]. *)
Inductive option (A : Set) : Set :=
| None
| Some (v : A).

Arguments None {A}.
(* This command asks Coq to *infer* the [A] type for each specific use of
 * [None]. *)

(* Here are a few example terms using [option]. *)
Example no_number : option nat := None.
Example a_number : option nat := Some 42.
Example no_number_squared : option (option nat) := None.
Example no_number_squared_inside : option (option nat) := Some None.
Example a_number_squared : option (option nat) := Some (Some 42).

(* Pattern matching is the key ingredient for working with inductive definitions
 * of all sorts.  Here are some examples matching on [option]s. *)

Definition increment_optional (no : option nat) : option nat :=
  match no with
  | None => None
  | Some n => Some (n + 1)
  end.

(* Here we use type [A * B] of *pairs*, inhabited by values [(a, b)], with
 * [a : A] and [b : B]. *)
Definition add_optional (po : option (nat * nat)) : option nat :=
  match po with
  | None => None
  | Some (n, m) => Some (n + m)
  end.


(** * Lists *)

(* For functional programming (as in Coq), the king of all generic data
 * structures is the *list*. *)
Inductive list (A : Set) : Set :=
| nil
| cons (hd : A) (tl : list A).

Arguments nil {A}.

(* [nil] is the empty list, while [cons], standing for "construct," extends a
 * list of length [n] into one of length [n+1]. *)

(* Here are some simple lists. *)

Example nats0 : list nat := nil.
Example nats1 : list nat := cons 1 nil.
Example nats2 : list nat := cons 1 (cons 2 nil).

(* Coq features a wonderful notation system, to help us write more concise and
 * readable code after introducing new syntactic forms.  We will not give a
 * systematic presentation of the notation system, but we will show many
 * examples, from which it is possible to infer generality by scientific
 * induction.  And, of course, the interested reader can always check the
 * notations chapter of the Coq reference manual. *)

(* First, our examples can get more readable with an infix operator for [cons]. *)

Infix "::" := cons.

Example nats1' : list nat := 1 :: nil.
Example nats2' : list nat := 1 :: 2 :: nil.

(* Getting even more fancy, we declare a notation for list literals. *)

Notation "[ ]" := nil.
Notation "[ x1 ; .. ; xN ]" := (cons x1 (.. (cons xN nil) ..)).

Example nats0'' : list nat := [].
Example nats1'' : list nat := [1].
Example nats2'' : list nat := [1; 2].
Example nats3'' : list nat := [1; 2; 3].

(* Here are some classic recursive functions that operate over lists.
 * First, here is how to compute the length of a list.  We put *implicit*
 * function arguments in curly braces, asking Coq to infer them at call
 * sites. *)

Fixpoint length {A} (ls : list A) : nat :=
  match ls with
  | nil => 0
  | _ :: ls' => 1 + length ls'
  end.

(* Here are two classic recursive functions on lists. *)

(* First, concatenation: *)
Fixpoint app {A} (ls1 ls2 : list A) : list A :=
  match ls1 with
  | nil => ls2
  | x :: ls1' => x :: app ls1' ls2
  end.

Infix "++" := app.

(* Next, reversal: *)
Fixpoint rev {A} (ls : list A) : list A :=
  match ls with
  | nil => nil
  | x :: ls' => rev ls' ++ [x]
  end.

Theorem length_app : forall A (ls1 ls2 : list A),
    length (ls1 ++ ls2) = length ls1 + length ls2.
Proof.
  induct ls1; simplify; equality.
Qed.

(* One of the classic gotchas in functional-programming class is how slow this
 * naive [rev] is.  Each [app] operation requires linear time, so running
 * linearly many [app]s brings us to quadratic time for [rev].  Using a helper
 * function, we can bring [rev] to its optimal linear time. *)

Fixpoint rev_append {A} (ls acc : list A) : list A :=
  match ls with
  | nil => acc
  | x :: ls' => rev_append ls' (x :: acc)
  end.

(* This function [rev_append] takes an extra *accumulator* argument, in which we
 * gradually build up the original input in reversed order.  The base case just
 * returns the accumulator.  Now reversal just needs to do a [rev_append] with
 * an empty initial accumulator. *)

Definition rev' {A} (ls : list A) : list A :=
  rev_append ls [].

(* A few test cases can help convince us that this seems to work. *)

Compute rev [1; 2; 3; 4].
Compute rev' [1; 2; 3; 4].
Compute rev ["hi"; "bye"; "sky"].
Compute rev' ["hi"; "bye"; "sky"].

(* OK, great.  Now it seems worth investing in a correctness proof.  We'll
 * discover it interactively in class, but here's a worked-out final
 * answer, with the several lemmas that we discover are useful. *)

(* List concatenation is associative. *)
Lemma app_assoc : forall A (ls1 ls2 ls3 : list A),
    (ls1 ++ ls2) ++ ls3 = ls1 ++ (ls2 ++ ls3).
Proof.
  induct ls1; simplify.

  equality.

  rewrite IHls1.
  equality.
Qed.

(* The natural correctness condition for [rev_append]: it does what it says on
 * the package, combining reversal with appending! *)
Lemma rev_append_ok : forall A (ls acc : list A),
    rev_append ls acc = rev ls ++ acc.
Proof.
  induct ls; simplify.

  equality.

  rewrite IHls.
  simplify.
  rewrite app_assoc.
  simplify.
  equality.
Qed.

(* IMPORTANT NOTE: the proof above would *not* have worked with the orders of
 * variables [ls] and [acc] swapped in the lemma statement!  Try the proof that
 * way to see what goes wrong.  The problem is that the induction hypothesis
 * would be too weak.  A single [acc] value would be fixed for the whole proof,
 * while we need [acc] to *vary* throughout the induction, by retaining a
 * universal quantifier for it in the IH. *)

(* Concatenating the empty list has no effect. *)
Lemma app_nil : forall A (ls : list A),
    ls ++ [] = ls.
Proof.
  induct ls; simplify.

  equality.

  equality.
Qed.

(* Now we can prove equivalence of [rev'] and [rev], with no new induction. *)
Theorem rev'_ok : forall A (ls : list A),
    rev' ls = rev ls.
Proof.
  simplify.
  unfold rev'.
  rewrite rev_append_ok.
  apply app_nil.
Qed.

(** ** Zipping and unzipping *)

(* Another classic pair of list operations is zipping and unzipping.
 * These functions convert between pairs of lists and lists of pairs. *)

Fixpoint zip {A1 A2} (ls1 : list A1) (ls2 : list A2) : list (A1 * A2) :=
  match ls1, ls2 with
  | x1 :: ls1', x2 :: ls2' => (x1, x2) :: zip ls1' ls2'
  | _, _ => []
  end.
(* Note how, when passed two lengths of different lists, [zip] drops the
 * mismatched suffix of the longer list. *)

(* An explicit [Set] annotation is needed here, for obscure type-inference
 * reasons. *)
Fixpoint unzip {A1 A2 : Set} (ls : list (A1 * A2)) : list A1 * list A2 :=
  match ls with
  | [] => ([], [])
  | (x1, x2) :: ls' =>
    let (ls1, ls2) := unzip ls' in
    (x1 :: ls1, x2 :: ls2)
  end.

(* A few common-sense properties hold of these definitions. *)

Theorem length_zip : forall A1 A2 (ls1 : list A1) (ls2 : list A2),
    length (zip ls1 ls2) = min (length ls1) (length ls2).
Proof.
  induct ls1; simplify.

  linear_arithmetic.

  cases ls2; simplify.

  linear_arithmetic.

  rewrite IHls1.
  linear_arithmetic.
Qed.

(* We write [fst] and [snd] for the first and second projection operators on
 * pairs, respectively. *)

Theorem length_unzip1 : forall (A1 A2 : Set) (ls : list (A1 * A2)),
    length (fst (unzip ls)) = length ls.
Proof.
  induct ls; simplify.

  equality.

  cases hd.
  (* Note that [cases] allows us to pull apart a pair into its two pieces. *)
  cases (unzip ls).
  simplify.
  equality.
Qed.

Theorem length_unzip2 : forall (A1 A2 : Set) (ls : list (A1 * A2)),
    length (snd (unzip ls)) = length ls.
Proof.
  induct ls; simplify.

  equality.

  cases hd.
  cases (unzip ls).
  simplify.
  equality.
Qed.

Theorem zip_unzip : forall (A1 A2 : Set) (ls : list (A1 * A2)),
    (let (ls1, ls2) := unzip ls in zip ls1 ls2) = ls.
Proof.
  induct ls; simplify.

  equality.

  cases hd.
  cases (unzip ls).
  simplify.
  equality.
Qed.

(* There are also interesting interactions with [app] and [rev]. *)

Theorem unzip_app : forall (A1 A2 : Set) (x y : list (A1 * A2)),
    unzip (x ++ y)
    = (let (x1, x2) := unzip x in
       let (y1, y2) := unzip y in
       (x1 ++ y1, x2 ++ y2)).
Proof.
  induct x; simplify.

  cases (unzip y).
  equality.

  cases hd.
  cases (unzip x).
  simplify.
  rewrite IHx.
  cases (unzip y).
  equality.
Qed.

Theorem unzip_rev : forall (A1 A2 : Set) (ls : list (A1 * A2)),
    unzip (rev ls) = (let (ls1, ls2) := unzip ls in
                      (rev ls1, rev ls2)).
Proof.
  induct ls; simplify.

  equality.

  cases hd.
  cases (unzip ls).
  simplify.
  rewrite unzip_app.
  rewrite IHls.
  simplify.
  equality.
Qed.


(** * Binary trees *)

(* Another classic datatype is binary trees, which we can define like so. *)
Inductive tree (A : Set) : Set :=
| Leaf
| Node (l : tree A) (d : A) (r : tree A).

Arguments Leaf {A}.

Example tr1 : tree nat := Node (Node Leaf 7 Leaf) 8 (Node Leaf 9 (Node Leaf 10 Leaf)).

(* There is a natural notion of size of a tree. *)
Fixpoint size {A} (t : tree A) : nat :=
  match t with
  | Leaf => 0
  | Node l _ r => 1 + size l + size r
  end.

(* There is also a natural sense of reversing a tree, flipping it around its
 * vertical axis. *)
Fixpoint reverse {A} (t : tree A) : tree A :=
  match t with
  | Leaf => Leaf
  | Node l d r => Node (reverse r) d (reverse l)
  end.

(* There is a natural relationship between the two. *)
Theorem size_reverse : forall A (t : tree A),
    size (reverse t) = size t.
Proof.
  induct t; simplify.

  equality.

  linear_arithmetic.
Qed.

(* Another classic tree operation is flattening into lists. *)
Fixpoint flatten {A} (t : tree A) : list A :=
  match t with
  | Leaf => []
  | Node l d r => flatten l ++ d :: flatten r
  end.
(* Note here that operators [++] and [::] are right-associative. *)

Theorem length_flatten : forall A (t : tree A),
    length (flatten t) = size t.
Proof.
  induct t; simplify.

  equality.

  rewrite length_app.
  simplify.
  linear_arithmetic.
Qed.

Lemma rev_app : forall A (ls1 ls2 : list A),
    rev (ls1 ++ ls2) = rev ls2 ++ rev ls1.
Proof.
  induct ls1; simplify.

  rewrite app_nil.
  equality.

  rewrite IHls1.
  apply app_assoc.
Qed.

Theorem rev_flatten : forall A (t : tree A),
    rev (flatten t) = flatten (reverse t).
Proof.
  induct t; simplify.

  equality.

  rewrite rev_app.
  simplify.
  rewrite app_assoc.
  simplify.
  equality.
Qed.


(** * Syntax trees *)

(* Trees are particularly important to us in studying program proof, since it is
 * natural to represent programs as *syntax trees*.  Here's a quick example, for
 * a tiny imperative language. *)

Inductive expression : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : expression)
| Minus (e1 e2 : expression)
| Times (e1 e2 : expression)
| GreaterThan (e1 e2 : expression)
| Not (e : expression).

Inductive statement : Set :=
| Assign (x : var) (e : expression)
| Sequence (s1 s2 : statement)
| IfThenElse (e : expression) (s1 s2 : statement)
| WhileLoop (e : expression) (s : statement).

(* First, here's a quick sample of nifty notations to write
 * almost-natural-looking embedded programs in Coq. *)
Coercion Const : nat >-> expression.
Coercion Var : string >-> expression.
(*Declare Scope embedded_scope.*)
Infix "+" := Plus : embedded_scope.
Infix "-" := Minus : embedded_scope.
Infix "*" := Times : embedded_scope.
Infix ">" := GreaterThan : embedded_scope.
Infix "<-" := Assign (at level 75) : embedded_scope.
Infix ";" := Sequence (at level 76) : embedded_scope.
Notation "'If' e {{ s1 }} 'else' {{ s2 }}" := (IfThenElse e s1 s2) (at level 75) : embedded_scope.
Notation "'While' e {{ s }}" := (WhileLoop e s) (at level 75) : embedded_scope.
Delimit Scope embedded_scope with embedded.

Example factorial :=
  ("answer" <- 1;
   While ("input" > 0) {{
     "answer" <- "answer" * "input";
     "input" <- "input" - 1
   }})%embedded.

(* A variety of compiler-style operations can be coded on top of this type.
 * Here's one to count total variable occurrences. *)

Fixpoint varsInExpression (e : expression) : nat :=
  match e with
  | Const _ => 0
  | Var _ => 1
  | Plus e1 e2
  | Minus e1 e2
  | Times e1 e2
  | GreaterThan e1 e2 => varsInExpression e1 + varsInExpression e2
  | Not e1 => varsInExpression e1
  end.

Fixpoint varsInStatement (s : statement) : nat :=
  match s with
  | Assign _ e => 1 + varsInExpression e
  | Sequence s1 s2 => varsInStatement s1 + varsInStatement s2
  | IfThenElse e s1 s2 => varsInExpression e + varsInStatement s1 + varsInStatement s2
  | WhileLoop e s1 => varsInExpression e + varsInStatement s1
  end.

(* We will need to wait for a few more lectures' worth of conceptual progress
 * before we can prove that transformations on programs preserve meaning, but we
 * do already have enough tools that prove that transformations preserve more
 * basic properties, like number of variables.  Here's one such transformation,
 * which flips "then" and "else" cases while also negating "if" conditions. *)
Fixpoint flipper (s : statement) : statement :=
  match s with
  | Assign _ _ => s
  | Sequence s1 s2 => Sequence (flipper s1) (flipper s2)
  | IfThenElse e s1 s2 => IfThenElse (Not e) (flipper s2) (flipper s1)
  | WhileLoop e s1 => WhileLoop e (flipper s1)
  end.

Theorem varsIn_flipper : forall s,
    varsInStatement (flipper s) = varsInStatement s.
Proof.
  induct s; simplify.

  equality.

  equality.

  linear_arithmetic.

  equality.
Qed.

(* Just for the sheer madcap fun of it, let's write some translations of
 * programs into our lists from before, with variables as data values. *)

Fixpoint listifyExpression (e : expression) : list var :=
  match e with
  | Const _ => []
  | Var x => [x]
  | Plus e1 e2
  | Minus e1 e2
  | Times e1 e2
  | GreaterThan e1 e2 => listifyExpression e1 ++ listifyExpression e2
  | Not e1 => listifyExpression e1
  end.

Fixpoint listifyStatement (s : statement) : list var :=
  match s with
  | Assign x e => x :: listifyExpression e
  | Sequence s1 s2 => listifyStatement s1 ++ listifyStatement s2
  | IfThenElse e s1 s2 => listifyExpression e ++ listifyStatement s1 ++ listifyStatement s2
  | WhileLoop e s1 => listifyExpression e ++ listifyStatement s1
  end.

Compute listifyStatement factorial.

(* At this point, I can't resist switching to a more automated proof style,
 * though still a pretty tame one. *)

Hint Rewrite length_app.

Lemma length_listifyExpression : forall e,
    length (listifyExpression e) = varsInExpression e.
Proof.
  induct e; simplify; linear_arithmetic.
Qed.

Hint Rewrite length_listifyExpression.

Theorem length_listifyStatement : forall s,
    length (listifyStatement s) = varsInStatement s.
Proof.
  induct s; simplify; linear_arithmetic.
Qed.

(* Other transformations are also possible, like the Swedish-Chef optimization,
 * which turns every variable into "bork".  It saves many bits when most variable
 * names are longer than 4 characters. *)

Fixpoint swedishExpression (e : expression) : expression :=
  match e with
  | Const _ => e
  | Var _ => Var "bork"
  | Plus e1 e2 => Plus (swedishExpression e1) (swedishExpression e2)
  | Minus e1 e2 => Minus (swedishExpression e1) (swedishExpression e2)
  | Times e1 e2 => Times (swedishExpression e1) (swedishExpression e2)
  | GreaterThan e1 e2 => GreaterThan (swedishExpression e1) (swedishExpression e2)
  | Not e1 => Not (swedishExpression e1)
  end.

Fixpoint swedishStatement (s : statement) : statement :=
  match s with
  | Assign _ e => Assign "bork" (swedishExpression e)
  | Sequence s1 s2 => Sequence (swedishStatement s1) (swedishStatement s2)
  | IfThenElse e s1 s2 => IfThenElse (swedishExpression e) (swedishStatement s1) (swedishStatement s2)
  | WhileLoop e s1 => WhileLoop (swedishExpression e) (swedishStatement s1)
  end.

Compute swedishStatement factorial.

Fixpoint swedishList (ls : list var) : list var :=
  match ls with
  | [] => []
  | _ :: ls => "bork" :: swedishList ls
  end.

Lemma swedishList_app : forall ls1 ls2,
    swedishList (ls1 ++ ls2) = swedishList ls1 ++ swedishList ls2.
Proof.
  induct ls1; simplify; equality.
Qed.

Hint Rewrite swedishList_app.

Lemma listifyExpression_swedishExpression : forall e,
    listifyExpression (swedishExpression e) = swedishList (listifyExpression e).
Proof.
  induct e; simplify; equality.
Qed.

Hint Rewrite listifyExpression_swedishExpression.

Lemma listifyStatement_swedishStatement : forall s,
    listifyStatement (swedishStatement s) = swedishList (listifyStatement s).
Proof.
  induct s; simplify; equality.
Qed.
