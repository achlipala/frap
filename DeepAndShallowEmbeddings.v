(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 13: Deep and Shallow Embeddings
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Shared notations and definitions; main material starts afterward. *)

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
Definition heap := fmap nat nat.
Definition assertion := heap -> Prop.

Hint Extern 1 (_ <= _) => linear_arithmetic : core.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic : core.

Example h0 : heap := $0 $+ (0, 2) $+ (1, 1) $+ (2, 8) $+ (3, 6).

Hint Rewrite max_l max_r using linear_arithmetic : core.

Ltac simp := repeat (simplify; subst; propositional;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         end); try linear_arithmetic.


(** * Basic concepts of shallow, deep, and mixed embeddings *)

(* We often have many options for how to encode some sort of formal expression.
 * The simplest way is to write it directly as a Gallina functional program,
 * which Coq knows how to evaluate directly.  That style is called
 * *shallow embedding*. *)

Module SimpleShallow.
  Definition foo (x y : nat) : nat :=
    let u := x + y in
    let v := u * y in
    u + v.
End SimpleShallow.

(* Alternatively, we can do as we have been through most of the chapters: define
 * inductive types of program syntax, along with semantics for syntax trees.
 * That style is called *deep embedding*. *)

Module SimpleDeep.
  Inductive exp :=
  | Const (n : nat)
  | Var (x : var)
  | Plus (e1 e2 : exp)
  | Times (e1 e2 : exp)
  | Let (x : var) (e1 e2 : exp).

  Definition foo : exp :=
    Let "u" (Plus (Var "x") (Var "y"))
        (Let "v" (Times (Var "u") (Var "y"))
             (Plus (Var "u") (Var "v"))).

  Fixpoint interp (e : exp) (v : fmap var nat) : nat :=
    match e with
    | Const n => n
    | Var x => v $! x
    | Plus e1 e2 => interp e1 v + interp e2 v
    | Times e1 e2 => interp e1 v * interp e2 v
    | Let x e1 e2 => interp e2 (v $+ (x, interp e1 v))
    end.
End SimpleDeep.

(* We defined function [foo] in shallow and deep styles, and it is easy to prove
 * that the encodings are equivalent. *)
Theorem shallow_to_deep : forall x y,
    SimpleShallow.foo x y = SimpleDeep.interp SimpleDeep.foo ($0 $+ ("x", x) $+ ("y", y)).
Proof.
  unfold SimpleShallow.foo.
  simplify.
  reflexivity.
Qed.

(* More interestingly, we can mix characteristics of the two styles.  To explain
 * exactly how, it's important to introduce the distinction between the
 * *metalanguage*, in which we do our proofs (e.g., Coq for us); and the
 * *object language*, which we formalize explicitly (e.g., lambda calculus,
 * simple imperative programs, ...).  With *higher-order abstract syntax*, we
 * represent binders of the object language using the function types of the
 * metalanguage. *)
Module SimpleMixed.
  Inductive exp :=
  | Const (n : nat)
  | Var (x : string)
  | Plus (e1 e2 : exp)
  | Times (e1 e2 : exp)
  | Let (e1 : exp) (e2 : nat -> exp).
  (* Note a [Let] body is a *function* over the computed value attached to the
   * variable being bound. *)

  Definition foo : exp :=
    Let (Plus (Var "x") (Var "y"))
        (fun u => Let (Times (Const u) (Var "y"))
                      (fun v => Plus (Const u) (Const v))).

  Fixpoint interp (e : exp) (v : fmap var nat) : nat :=
    match e with
    | Var x => v $! x
    | Const n => n
    | Plus e1 e2 => interp e1 v + interp e2 v
    | Times e1 e2 => interp e1 v * interp e2 v
    | Let e1 e2 => interp (e2 (interp e1 v)) v
    end.

  (* We can even do useful transformations on such expressions within Gallina,
   * as in this function to recursively simplify additions of 0 and
   * multiplications by 1. *)
  Fixpoint reduce (e : exp) : exp :=
    match e with
    | Var x => Var x
    | Const n => Const n
    | Plus e1 e2 =>
      let e1' := reduce e1 in
      let e2' := reduce e2 in
      match e1' with
      | Const 0 => e2'
      | _ => match e2' with
             | Const 0 => e1'
             | _ => Plus e1' e2'
             end
      end
    | Times e1 e2 =>
      let e1' := reduce e1 in
      let e2' := reduce e2 in
      match e1' with
      | Const 1 => e2'
      | _ => match e2' with
             | Const 1 => e1'
             | _ => Times e1' e2'
             end
      end
    | Let e1 e2 =>
      let e1' := reduce e1 in
      match e1' with
      | Const n => reduce (e2 n)
      | _ => Let e1' (fun n => reduce (e2 n))
      end
    end.

  (* This example shows simplification, even under binders. *)
  Compute (reduce (Let (Plus (Const 0) (Const 1))
                       (fun n => Let (Times (Var "x") (Const 2))
                                     (fun m => Times (Const n) (Const m))))).

  (* The transformation is provably meaning-preserving. *)
  Theorem reduce_ok : forall v e, interp (reduce e) v = interp e v.
  Proof.
    induct e; simplify;
    repeat match goal with
           | [ H : _ = interp _ _ |- _ ] => rewrite <- H
           | [ |- context[match ?E with _ => _ end] ] => cases E; simplify; subst; try linear_arithmetic
    end; eauto.
  Qed.
End SimpleMixed.

Theorem shallow_to_mixed : forall x y,
    SimpleShallow.foo x y = SimpleMixed.interp SimpleMixed.foo ($0 $+ ("x", x) $+ ("y", y)).
Proof.
  unfold SimpleShallow.foo.
  simplify.
  reflexivity.
Qed.


(** * Shallow embedding of a language very similar to the one we used last chapter *)

(* With the basic terminology out of the way, let's see these ideas in action,
 * to encode the sort of imperative language we studied in the previous
 * chapter. *)

Module Shallow.
  (* As a shallow embedding, we can represent imperative programs as functional
   * programs that manipulate heaps explicitly. *)
  Definition cmd result := heap -> heap * result.
  (* Parameter [result] gives the type of the value being computed by a
   * command.  The command is a function taking the initial heap as input, and
   * it returns a pair of the final heap and the command's result. *)

  (* We can redefine Hoare triples over these functional programs. *)
  Definition hoare_triple (P : assertion) {result} (c : cmd result) (Q : result -> assertion) :=
    forall h, P h
              -> let (h', r) := c h in
                 Q r h'.

  Notation "{{ h ~> P }} c {{ r & h' ~> Q }}" :=
    (hoare_triple (fun h => P) c (fun r h' => Q)) (at level 90, c at next level).

  (* Standard rules of Hoare logic can be proved as lemmas.  For instance,
   * here's the rule of consequence. *)
  Theorem consequence : forall P {result} (c : cmd result) Q
                               (P' : assertion) (Q' : _ -> assertion),
      hoare_triple P c Q
      -> (forall h, P' h -> P h)
      -> (forall r h, Q r h -> Q' r h)
      -> hoare_triple P' c Q'.
  Proof.
    unfold hoare_triple; simplify.
    specialize (H h).
    specialize (H0 h).
    cases (c h).
    auto.
  Qed.

  (* However, the programs themselves look quite different from those we saw in
   * the previous chapter.  This function computes the maximum among the first [i]
   * cells of memory and the accumulator [acc]. *)
  Fixpoint array_max (i acc : nat) : cmd nat :=
    fun h =>
      match i with
      | O => (h, acc)
      | S i' =>
        let h_i' := h $! i' in
        array_max i' (max h_i' acc) h
      end.

  (* We can prove its correctness via preconditions and postconditions. *)

  Lemma array_max_ok' : forall len i acc,
    {{ h ~> forall j, i <= j < len -> h $! j <= acc }}
      array_max i acc
    {{ r&h ~> forall j, j < len -> h $! j <= r }}.
  Proof.
    induct i; unfold hoare_triple in *; simplify; propositional; auto.

    specialize (IHi (max (h $! i) acc) h); propositional.
    cases (array_max i (max (h $! i) acc) h); simplify; propositional; subst.
    apply IHi; auto.
    simplify.
    cases (j0 ==n i); subst; auto.
    assert (h $! j0 <= acc) by auto.
    linear_arithmetic.
  Qed.

  Theorem array_max_ok : forall len,
    {{ _ ~> True }}
      array_max len 0
    {{ r&h ~> forall i, i < len -> h $! i <= r }}.
  Proof.
    simplify.
    eapply consequence.
    apply array_max_ok' with (len := len).

    simplify.
    linear_arithmetic.

    auto.
  Qed.

  (* We can also run the program on concrete inputs. *)
  Example run_array_max0 : array_max 4 0 h0 = (h0, 8).
  Proof.
    unfold h0.
    simplify.
    reflexivity.
  Qed.

  (* One more example in the same style: increment each of the first [i] cells
   * of memory. *)

  Fixpoint increment_all (i : nat) : cmd unit :=
    fun h =>
      match i with
      | O => (h, tt)
      | S i' => increment_all i' (h $+ (i', S (h $! i')))
      end.

  Lemma increment_all_ok' : forall len h0 i,
    {{ h ~> (forall j, j < i -> h $! j = h0 $! j)
       /\ (forall j, i <= j < len -> h $! j = S (h0 $! j)) }}
      increment_all i
    {{ _&h ~> forall j, j < len -> h $! j = S (h0 $! j) }}.
  Proof.
    induct i; unfold hoare_triple in *; simplify; propositional; auto.

    specialize (IHi (h $+ (i, S (h $! i)))); propositional.
    cases (increment_all i (h $+ (i, S (h $! i)))); simplify; propositional; subst.
    apply H; simplify; auto.

    cases (j0 ==n i); subst; auto.
    simplify; auto.
    simplify; auto.
  Qed.

  Theorem increment_all_ok : forall len h0,
    {{ h ~> h = h0 }}
      increment_all len
    {{ _&h ~> forall j, j < len -> h $! j = S (h0 $! j) }}.
  Proof.
    simplify.
    eapply consequence.
    apply increment_all_ok' with (len := len).

    simplify; subst; propositional.
    linear_arithmetic.

    simplify.
    auto.
  Qed.

  Example run_increment_all0 : increment_all 4 h0 = ($0 $+ (0, 3) $+ (1, 2) $+ (2, 9) $+ (3, 7), tt).
  Proof.
    unfold h0.
    simplify.
    f_equal.
    maps_equal.
  Qed.
End Shallow.


(** * A basic deep embedding *)

(* One disadvantage of the last style of programs is computational efficiency:
 * real CPU architectures don't manipulate memory as functional maps that are
 * passed around, and the abstraction gap between our code and CPUs prevents us
 * from taking maximum advantage of the hardware to achieve good performance.
 * To help regain that efficiency, let's do a deep embedding of the language.
 * Actually, it's a mixed embedding, with no explicit concept of variables,
 * using higher-order abstract syntax to represent binders. *)

Module Deep.
  Inductive cmd : Set -> Type :=
  | Return {result : Set} (r : result) : cmd result
  | Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
  | Read (a : nat) : cmd nat
  | Write (a v : nat) : cmd unit.

  (* These constructors are most easily explained through examples.  We'll
   * translate both of the programs from the shallow embedding above. *)

  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).

  Fixpoint array_max (i acc : nat) : cmd nat :=
    match i with
    | O => Return acc
    | S i' =>
      h_i' <- Read i';
      array_max i' (max h_i' acc)
    end.

  Fixpoint increment_all (i : nat) : cmd unit :=
    match i with
    | O => Return tt
    | S i' =>
      v <- Read i';
      _ <- Write i' (S v); 
      increment_all i'
    end.

  (* Note how this is truly a mixed encoding: we freely use Gallina constructs
   * like [match], mixed in with instructions specific to the object language,
   * like reading or writing memory.  An interpreter explains what it all means,
   * reducing programs to their original type from the shallow embedding. *)

  Fixpoint interp {result} (c : cmd result) (h : heap) : heap * result :=
    match c with
    | Return _ r => (h, r)
    | Bind _ _ c1 c2 =>
      let (h', r) := interp c1 h in
      interp (c2 r) h'
    | Read a => (h, h $! a)
    | Write a v => (h $+ (a, v), tt)
    end.

  Example run_array_max0 : interp (array_max 4 0) h0 = (h0, 8).
  Proof.
    unfold h0.
    simplify.
    reflexivity.
  Qed.

  Example run_increment_all0 : interp (increment_all 4) h0 = ($0 $+ (0, 3) $+ (1, 2) $+ (2, 9) $+ (3, 7), tt).
  Proof.
    unfold h0.
    simplify.
    f_equal.
    maps_equal.
  Qed.

  (* This time, we define a Hoare-triple relation syntactically. *)
  Inductive hoare_triple : assertion -> forall {result}, cmd result -> (result -> assertion) -> Prop :=
  | HtReturn : forall P {result : Set} (v : result),
      hoare_triple P (Return v) (fun r h => P h /\ r = v)

  | HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
      hoare_triple P c1 Q
      -> (forall r, hoare_triple (Q r) (c2 r) R)
      -> hoare_triple P (Bind c1 c2) R
    (* Interesting thing about this rule: the second premise uses nested
     * universal quantification over all possible results of the first command. *)

  | HtRead : forall P a,
      hoare_triple P (Read a) (fun r h => P h /\ r = h $! a)
  | HtWrite : forall P a v,
      hoare_triple P (Write a v) (fun _ h => exists h', P h' /\ h = h' $+ (a, v))
  | HtConsequence : forall {result} (c : cmd result) P Q (P' : assertion) (Q' : _ -> assertion),
      hoare_triple P c Q
      -> (forall h, P' h -> P h)
      -> (forall r h, Q r h -> Q' r h)
      -> hoare_triple P' c Q'.

  Lemma HtStrengthen : forall {result} (c : cmd result) P Q (Q' : _ -> assertion),
      hoare_triple P c Q
      -> (forall r h, Q r h -> Q' r h)
      -> hoare_triple P c Q'.
  Proof.
    simplify.
    eapply HtConsequence; eauto.
  Qed.

  (* Here are a few tactics, whose details we won't explain, but which
   * streamline the individual program proofs below. *)
  Ltac basic := apply HtReturn || eapply HtRead || eapply HtWrite.
  Ltac step0 := basic || eapply HtBind || (eapply HtStrengthen; [ basic | ]).
  Ltac step := step0; simp.
  Ltac ht := simp; repeat step; eauto.
  Ltac conseq := simplify; eapply HtConsequence.
  Ltac use_IH H := conseq; [ apply H | .. ]; ht.
  
  Notation "{{ h ~> P }} c {{ r & h' ~> Q }}" :=
    (hoare_triple (fun h => P) c (fun r h' => Q)) (at level 90, c at next level).

  Lemma array_max_ok' : forall len i acc,
    {{ h ~> forall j, i <= j < len -> h $! j <= acc }}
      array_max i acc
    {{ r&h ~> forall j, j < len -> h $! j <= r }}.
  Proof.
    induct i; ht.
    use_IH IHi.
    cases (j ==n i); simp.
    assert (h $! j <= acc) by auto.
    linear_arithmetic.
  Qed.

  Theorem array_max_ok : forall len,
    {{ _ ~> True }}
      array_max len 0
    {{ r&h ~> forall i, i < len -> h $! i <= r }}.
  Proof.
    conseq.
    apply array_max_ok' with (len := len).
    simp.
    simp.
    auto.
  Qed.

  Lemma increment_all_ok' : forall len h0 i,
    {{ h ~> (forall j, j < i -> h $! j = h0 $! j)
       /\ (forall j, i <= j < len -> h $! j = S (h0 $! j)) }}
      increment_all i
    {{ _&h ~> forall j, j < len -> h $! j = S (h0 $! j) }}.
  Proof.
    induct i; ht.
    use_IH IHi.
    cases (j ==n i); simp.
    auto.
    auto.
  Qed.

  Theorem increment_all_ok : forall len h0,
    {{ h ~> h = h0 }}
      increment_all len
    {{ _&h ~> forall j, j < len -> h $! j = S (h0 $! j) }}.
  Proof.
    conseq.
    apply increment_all_ok' with (len := len).
    simp.
    simp.
    auto.
  Qed.

  (* It's easy to prove the syntactic Hoare-triple relation sound with
   * respect to the semantic one from the shallow embedding. *)
  Theorem hoare_triple_sound : forall P {result} (c : cmd result) Q,
      hoare_triple P c Q
      -> forall h, P h
                   -> let (h', r) := interp c h in
                      Q r h'.
  Proof.
    induct 1; simplify; propositional; eauto.

    specialize (IHhoare_triple h).
    cases (interp c1 h).
    apply H1; eauto.

    specialize (IHhoare_triple h).
    cases (interp c h).
    eauto.
  Qed.
End Deep.
(* We use Coq's *extraction* feature to produce OCaml versions of our deeply
 * embedded programs.  Then we can run them using OCaml intepreters, which are
 * able to take advantage of the side effects built into OCaml, as a
 * performance optimization.  This command generates file "Deep.ml", which can
 * be loaded along with "DeepInterp.ml" to run the generated code.  Note how
 * the latter file uses OCaml's built-in mutable hash-table type for efficient
 * representation of program memories. *)
Extraction "Deep.ml" Deep.array_max Deep.increment_all.


(** * A slightly fancier deep embedding, adding unbounded loops *)

Module Deeper.
  (* All programs in the last embedding must terminate, but let's add loops with
   * the potential to run forever, which takes us beyond what is representable
   * in the shallow embedding, since Gallina enforces termination for all
   * programs. *)

  (* We use this type to represent the outcome of a single loop iteration.
   * These are functional loops, where we successively modify an accumulator
   * value across iterations. *)
  Inductive loop_outcome acc :=
  | Done (a : acc)  (* The loop finished, and here is the final accumulator. *)
  | Again (a : acc) (* Keep looping, with this new accumulator. *).

  Inductive cmd : Set -> Type :=
  | Return {result : Set} (r : result) : cmd result
  | Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
  | Read (a : nat) : cmd nat
  | Write (a v : nat) : cmd unit
  | Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc.

  (* Again, it's all easier to explain with an example. *)

  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
  Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).

  (* This program finds the first occurrence in memory of value [needle]. *)
  Definition index_of (needle : nat) : cmd nat :=
    for i := 0 loop
      h_i <- Read i;
      if h_i ==n needle then
        Return (Done i)
      else
        Return (Again (S i))
    done.

  (* Next, we write a single-stepping interpreter for this language.  We can
   * no longer write a straightforward big-stepping interpeter, as programs of
   * the object language can diverge, while Gallina enforces termination. *)

  Inductive stepResult (result : Set) :=
  | Answer (r : result)
  | Stepped (h : heap) (c : cmd result). 

  Fixpoint step {result} (c : cmd result) (h : heap) : stepResult result :=
    match c with
    | Return _ r => Answer r
    | Bind _ _ c1 c2 =>
      match step c1 h with
      | Answer r => Stepped h (c2 r)
      | Stepped h' c1' => Stepped h' (Bind c1' c2)
      end
    | Read a => Answer (h $! a)
    | Write a v => Stepped (h $+ (a, v)) (Return tt)
    | Loop _ init body =>
      Stepped h (r <- body init;
                 match r with
                 | Done r' => Return r'
                 | Again r' => Loop r' body
                 end)
    end.

  Fixpoint multiStep {result} (c : cmd result) (h : heap) (n : nat) : stepResult result :=
    match n with
    | O => Stepped h c
    | S n' => match step c h with
              | Answer r => Answer r
              | Stepped h' c' => multiStep c' h' n'
              end
    end.

  Example run_index_of : multiStep (index_of 6) h0 20 = Answer 3.
  Proof.
    unfold h0.
    simplify.
    reflexivity.
  Qed.

  Inductive hoare_triple : assertion -> forall {result}, cmd result -> (result -> assertion) -> Prop :=
  | HtReturn : forall P {result : Set} (v : result),
      hoare_triple P (Return v) (fun r h => P h /\ r = v)
  | HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
      hoare_triple P c1 Q
      -> (forall r, hoare_triple (Q r) (c2 r) R)
      -> hoare_triple P (Bind c1 c2) R
  | HtRead : forall P a,
      hoare_triple P (Read a) (fun r h => P h /\ r = h $! a)
  | HtWrite : forall P a v,
      hoare_triple P (Write a v) (fun _ h => exists h', P h' /\ h = h' $+ (a, v))
  | HtConsequence : forall {result} (c : cmd result) P Q (P' : assertion) (Q' : _ -> assertion),
      hoare_triple P c Q
      -> (forall h, P' h -> P h)
      -> (forall r h, Q r h -> Q' r h)
      -> hoare_triple P' c Q'

  | HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc))
                    (I : loop_outcome acc -> assertion),
      (forall acc, hoare_triple (I (Again acc)) (body acc) I)
      -> hoare_triple (I (Again init)) (Loop init body) (fun r h => I (Done r) h).
  (* The loop rule contains a tricky new kind of invariant, parameterized on the
   * current loop state: either [Done] for a finished loop or [Again] for a loop
   * still in progress. *)

  Notation "{{ h ~> P }} c {{ r & h' ~> Q }}" :=
    (hoare_triple (fun h => P) c (fun r h' => Q)) (at level 90, c at next level).

  Lemma HtStrengthen : forall {result} (c : cmd result) P Q (Q' : _ -> assertion),
      hoare_triple P c Q
      -> (forall r h, Q r h -> Q' r h)
      -> hoare_triple P c Q'.
  Proof.
    simplify.
    eapply HtConsequence; eauto.
  Qed.

  Lemma HtWeaken : forall {result} (c : cmd result) P Q (P' : assertion),
      hoare_triple P c Q
      -> (forall h, P' h -> P h)
      -> hoare_triple P' c Q.
  Proof.
    simplify.
    eapply HtConsequence; eauto.
  Qed.

  Ltac basic := apply HtReturn || eapply HtRead || eapply HtWrite.
  Ltac step0 := basic || eapply HtBind || (eapply HtStrengthen; [ basic | ]).
  Ltac step := step0; simp.
  Ltac ht := simp; repeat step; eauto.
  Ltac conseq := simplify; eapply HtConsequence.
  Ltac use_IH H := conseq; [ apply H | .. ]; ht.
  Ltac loop_inv Inv := eapply HtConsequence; [ apply HtLoop with (I := Inv) | .. ]; ht.

  (* We prove our [index_of] example correct, relying crucially on a tactic
   * [loop_inv] to prove a loop by giving its loop invariant, which, recall, is
   * parameterized on a [loop_outcome]. *)
  Theorem index_of_ok : forall hinit needle,
    {{ h ~> h = hinit }}
      index_of needle
    {{ r&h ~> h = hinit
         /\ hinit $! r = needle
         /\ forall i, i < r -> hinit $! i <> needle }}.
  Proof.
    simplify.
    loop_inv (fun r h => h = hinit
                         /\ match r with
                            | Done r' => hinit $! r' = needle
                                         /\ forall i, i < r' -> hinit $! i <> needle
                            | Again r' => forall i, i < r' -> hinit $! i <> needle
                            end).
    cases (r ==n needle); ht.
    cases (i ==n acc); simp.
    apply H3 with (i0 := i); auto.
  Qed.

  (* The single-stepping interpreter forms the basis for defining transition
   * systems from commands. *)
  Definition trsys_of {result} (c : cmd result) (h : heap) := {|
    Initial := {(c, h)};
    Step := fun p1 p2 => step (fst p1) (snd p1) = Stepped (snd p2) (fst p2)
  |}.

  (* We now prove soundness of [hoare_triple], starting from a number of
   * inversion lemmas for it, collapsing the potential effects of many nested
   * rule-of-consequence applications. *)

  Lemma invert_Return : forall {result : Set} (r : result) P Q,
    hoare_triple P (Return r) Q
    -> forall h, P h -> Q r h.
  Proof.
    induct 1; propositional; eauto.
  Qed.

  Lemma invert_Bind : forall {result' result} (c1 : cmd result') (c2 : result' -> cmd result) P Q,
    hoare_triple P (Bind c1 c2) Q
    -> exists R, hoare_triple P c1 R
                 /\ forall r, hoare_triple (R r) (c2 r) Q.
  Proof.
    induct 1; propositional; eauto.

    invert IHhoare_triple; propositional.
    eexists; propositional.
    eapply HtWeaken.
    eassumption.
    auto.
    eapply HtStrengthen.
    apply H4.
    auto.
  Qed.

  (* Highly technical point: in some of the inductions below, we wind up needing
   * to show that the cases for [Read] and [Write] can never overlap, which
   * would imply that they have the same result types, which would mean that the
   * types [unit] and [nat] are equal. *)
  Lemma unit_not_nat : unit = nat -> False.
  Proof.
    simplify.
    assert (exists x : unit, forall y : unit, x = y).
    exists tt; simplify.
    cases y; reflexivity.
    rewrite H in H0.
    invert H0.
    specialize (H1 (S x)).
    linear_arithmetic.
  Qed.

  Lemma invert_Read : forall a P Q,
    hoare_triple P (Read a) Q
    -> forall h, P h -> Q (h $! a) h.
  Proof.
    induct 1; propositional; eauto.
    apply unit_not_nat in x0.
    propositional.
  Qed.

  Lemma invert_Write : forall a v P Q,
    hoare_triple P (Write a v) Q
    -> forall h, P h -> Q tt (h $+ (a, v)).
  Proof.
    induct 1; propositional; eauto.
    symmetry in x0.
    apply unit_not_nat in x0.
    propositional.
  Qed.

  Lemma invert_Loop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) P Q,
      hoare_triple P (Loop init body) Q
      -> exists I, (forall acc, hoare_triple (I (Again acc)) (body acc) I)
                   /\ (forall h, P h -> I (Again init) h)
                   /\ (forall r h, I (Done r) h -> Q r h).
  Proof.
    induct 1; propositional; eauto.

    invert IHhoare_triple; propositional.
    exists x; propositional; eauto.
  Qed.

  Lemma step_sound : forall {result} (c : cmd result) h Q,
      hoare_triple (fun h' => h' = h) c Q
      -> match step c h with
         | Answer r => Q r h
         | Stepped h' c' => hoare_triple (fun h'' => h'' = h') c' Q
         end.
  Proof.
    induct c; simplify; propositional.

    eapply invert_Return.
    eauto.
    simplify; auto.

    apply invert_Bind in H0.
    invert H0; propositional.
    apply IHc in H0.
    cases (step c h); auto.
    econstructor.
    apply H2.
    equality.
    auto.
    econstructor; eauto.

    eapply invert_Read; eauto.
    simplify; auto.

    eapply HtStrengthen.
    econstructor.
    simplify; propositional; subst.
    eapply invert_Write; eauto.
    simplify; auto.

    apply invert_Loop in H0.
    invert H0; propositional.
    econstructor.
    eapply HtWeaken.
    apply H0.
    equality.
    simplify.
    cases r.
    eapply HtStrengthen.
    econstructor.
    simplify.
    propositional; subst; eauto.
    eapply HtStrengthen.
    eapply HtLoop.
    auto.
    simplify.
    eauto.
  Qed.

  (* Clever choice of strengthened invariant here: intermediate commands are
   * checked against degenerate preconditions that force equality to the current
   * heap, and the postcondition is preserved across all steps. *)
  Lemma hoare_triple_sound' : forall P {result} (c : cmd result) Q,
      hoare_triple P c Q
      -> forall h, P h
                   -> invariantFor (trsys_of c h)
                                   (fun p => hoare_triple (fun h => h = snd p)
                                                          (fst p)
                                                          Q).
  Proof.
    simplify.

    apply invariant_induction; simplify.

    propositional; subst; simplify.
    eapply HtConsequence.
    eassumption.
    equality.
    auto.

    eapply step_sound in H1.
    rewrite H2 in H1.
    auto.
  Qed.

  (* Proving: if we reach a [Return] state, the postcondition holds. *)
  Theorem hoare_triple_sound : forall P {result} (c : cmd result) Q,
      hoare_triple P c Q
      -> forall h, P h
                   -> invariantFor (trsys_of c h)
                                   (fun p => forall r, fst p = Return r
                                                       -> Q r (snd p)).
  Proof.
    simplify.

    eapply invariant_weaken.
    eapply hoare_triple_sound'; eauto.
    simplify.
    rewrite H2 in H1.
    eapply invert_Return; eauto.
    simplify; auto.
  Qed.
End Deeper.

Extraction "Deeper.ml" Deeper.index_of.

(** * Adding the possibility of program failure *)

(* Let's model another effect that can be implemented using native OCaml
 * features.  We'll add a very basic form of exceptions, namely just one
 * (uncatchable) exception, for program failure.  We'll prove, by the end, that
 * verified programs never throw the exception. *)

Module DeeperWithFail.
  Inductive loop_outcome acc :=
  | Done (a : acc)
  | Again (a : acc).

  Inductive cmd : Set -> Type :=
  | Return {result : Set} (r : result) : cmd result
  | Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
  | Read (a : nat) : cmd nat
  | Write (a v : nat) : cmd unit
  | Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc
  | Fail {result} : cmd result.

  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
  Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).

  (* This program loops forever, maintaining a tally in memory address 0.
   * We periodically test that address, failing if it's ever found to be 0. *)
  Definition forever : cmd nat :=
    _ <- Write 0 1;
    for i := 1 loop
      h_i <- Read i;
      acc <- Read 0;
      match acc with
      | 0 => Fail
      | _ =>
        _ <- Write 0 (acc + h_i);
        Return (Again (i + 1))
      end
    done.

  (* We adapt our single-stepper with a new result kind, for failure. *)

  Inductive stepResult (result : Set) :=
  | Answer (r : result)
  | Stepped (h : heap) (c : cmd result)
  | Failed.

  Arguments Failed {result}.

  Fixpoint step {result} (c : cmd result) (h : heap) : stepResult result :=
    match c with
    | Return _ r => Answer r
    | Bind _ _ c1 c2 =>
      match step c1 h with
      | Answer r => Stepped h (c2 r)
      | Stepped h' c1' => Stepped h' (Bind c1' c2)
      | Failed => Failed
      end
    | Read a => Answer (h $! a)
    | Write a v => Stepped (h $+ (a, v)) (Return tt)
    | Loop _ init body =>
      Stepped h (r <- body init;
                 match r with
                 | Done r' => Return r'
                 | Again r' => Loop r' body
                 end)
    | Fail _ => Failed
    end.

  Fixpoint multiStep {result} (c : cmd result) (h : heap) (n : nat) : stepResult result :=
    match n with
    | O => Stepped h c
    | S n' => match step c h with
              | Answer r => Answer r
              | Stepped h' c' => multiStep c' h' n'
              | Failed => Failed
              end
    end.

  Inductive hoare_triple : assertion -> forall {result}, cmd result -> (result -> assertion) -> Prop :=
  | HtReturn : forall P {result : Set} (v : result),
      hoare_triple P (Return v) (fun r h => P h /\ r = v)
  | HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
      hoare_triple P c1 Q
      -> (forall r, hoare_triple (Q r) (c2 r) R)
      -> hoare_triple P (Bind c1 c2) R
  | HtRead : forall P a,
      hoare_triple P (Read a) (fun r h => P h /\ r = h $! a)
  | HtWrite : forall P a v,
      hoare_triple P (Write a v) (fun _ h => exists h', P h' /\ h = h' $+ (a, v))
  | HtConsequence : forall {result} (c : cmd result) P Q (P' : assertion) (Q' : _ -> assertion),
      hoare_triple P c Q
      -> (forall h, P' h -> P h)
      -> (forall r h, Q r h -> Q' r h)
      -> hoare_triple P' c Q'

  | HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) I,
      (forall acc, hoare_triple (I (Again acc)) (body acc) I)
      -> hoare_triple (I (Again init)) (Loop init body) (fun r h => I (Done r) h)

  | HtFail : forall {result},
      hoare_triple (fun _ => False) (Fail (result := result)) (fun _ _ => False).
    (* The rule for [Fail] simply enforces that this command can't be reachable,
     * since it gets an unsatisfiable precondition. *)

  Notation "{{ h ~> P }} c {{ r & h' ~> Q }}" :=
    (hoare_triple (fun h => P) c (fun r h' => Q)) (at level 90, c at next level).

  Lemma HtStrengthen : forall {result} (c : cmd result) P Q (Q' : _ -> assertion),
      hoare_triple P c Q
      -> (forall r h, Q r h -> Q' r h)
      -> hoare_triple P c Q'.
  Proof.
    simplify.
    eapply HtConsequence; eauto.
  Qed.

  Lemma HtWeaken : forall {result} (c : cmd result) P Q (P' : assertion),
      hoare_triple P c Q
      -> (forall h, P' h -> P h)
      -> hoare_triple P' c Q.
  Proof.
    simplify.
    eapply HtConsequence; eauto.
  Qed.

  Ltac basic := apply HtReturn || eapply HtRead || eapply HtWrite.
  Ltac step0 := basic || eapply HtBind || (eapply HtStrengthen; [ basic | ])
                || (eapply HtConsequence; [ apply HtFail | .. ]).
  Ltac step := step0; simp.
  Ltac ht := simp; repeat step.
  Ltac conseq := simplify; eapply HtConsequence.
  Ltac use_IH H := conseq; [ apply H | .. ]; ht.
  Ltac loop_inv0 Inv := (eapply HtWeaken; [ apply HtLoop with (I := Inv) | .. ])
                        || (eapply HtConsequence; [ apply HtLoop with (I := Inv) | .. ]).
  Ltac loop_inv Inv := loop_inv0 Inv; ht.

  Theorem forever_ok :
    {{ _ ~> True }}
      forever
    {{ _&_ ~> False }}.
  Proof.
    ht.
    loop_inv (fun (r : loop_outcome nat) h => h $! 0 > 0 /\ match r with
                                                            | Done _ => False
                                                            | _ => True
                                                            end).
    cases r1; ht.
  Qed.

  Definition trsys_of {result} (c : cmd result) (h : heap) := {|
    Initial := {(c, h)};
    Step := fun p1 p2 => step (fst p1) (snd p1) = Stepped (snd p2) (fst p2)
  |}.

  (* Next, we adapt the proof of soundness from before. *)

  Lemma invert_Return : forall {result : Set} (r : result) P Q,
    hoare_triple P (Return r) Q
    -> forall h, P h -> Q r h.
  Proof.
    induct 1; propositional; eauto.
  Qed.

  Lemma invert_Bind : forall {result' result} (c1 : cmd result') (c2 : result' -> cmd result) P Q,
    hoare_triple P (Bind c1 c2) Q
    -> exists R, hoare_triple P c1 R
                 /\ forall r, hoare_triple (R r) (c2 r) Q.
  Proof.
    induct 1; propositional; eauto.

    invert IHhoare_triple; propositional.
    eexists; propositional.
    eapply HtWeaken.
    eassumption.
    auto.
    eapply HtStrengthen.
    apply H4.
    auto.
  Qed.

  Lemma unit_not_nat : unit = nat -> False.
  Proof.
    simplify.
    assert (exists x : unit, forall y : unit, x = y).
    exists tt; simplify.
    cases y; reflexivity.
    rewrite H in H0.
    invert H0.
    specialize (H1 (S x)).
    linear_arithmetic.
  Qed.

  Lemma invert_Read : forall a P Q,
    hoare_triple P (Read a) Q
    -> forall h, P h -> Q (h $! a) h.
  Proof.
    induct 1; propositional; eauto.
    apply unit_not_nat in x0.
    propositional.
  Qed.

  Lemma invert_Write : forall a v P Q,
    hoare_triple P (Write a v) Q
    -> forall h, P h -> Q tt (h $+ (a, v)).
  Proof.
    induct 1; propositional; eauto.
    symmetry in x0.
    apply unit_not_nat in x0.
    propositional.
  Qed.

  Lemma invert_Loop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) P Q,
      hoare_triple P (Loop init body) Q
      -> exists I, (forall acc, hoare_triple (I (Again acc)) (body acc) I)
                   /\ (forall h, P h -> I (Again init) h)
                   /\ (forall r h, I (Done r) h -> Q r h).
  Proof.
    induct 1; propositional; eauto.

    invert IHhoare_triple; propositional.
    exists x; propositional; eauto.
  Qed.

  Lemma invert_Fail : forall result P Q,
    hoare_triple P (Fail (result := result)) Q
    -> forall h, P h -> False.
  Proof.
    induct 1; propositional; eauto.
  Qed.

  Lemma step_sound : forall {result} (c : cmd result) h Q,
      hoare_triple (fun h' => h' = h) c Q
      -> match step c h with
         | Answer r => Q r h
         | Stepped h' c' => hoare_triple (fun h'' => h'' = h') c' Q
         | Failed => False
         end.
  Proof.
    induct c; simplify; propositional.

    eapply invert_Return.
    eauto.
    simplify; auto.

    apply invert_Bind in H0.
    invert H0; propositional.
    apply IHc in H0.
    cases (step c h); auto.
    econstructor.
    apply H2.
    equality.
    auto.
    econstructor; eauto.

    eapply invert_Read; eauto.
    simplify; auto.

    eapply HtStrengthen.
    econstructor.
    simplify; propositional; subst.
    eapply invert_Write; eauto.
    simplify; auto.

    apply invert_Loop in H0.
    invert H0; propositional.
    econstructor.
    eapply HtWeaken.
    apply H0.
    equality.
    simplify.
    cases r.
    eapply HtStrengthen.
    econstructor.
    simplify.
    propositional; subst; eauto.
    eapply HtStrengthen.
    eapply HtLoop.
    auto.
    simplify.
    eauto.

    eapply invert_Fail; eauto.
    simplify; eauto.
  Qed.

  Lemma hoare_triple_sound' : forall P {result} (c : cmd result) Q,
      hoare_triple P c Q
      -> forall h, P h
                   -> invariantFor (trsys_of c h)
                                   (fun p => hoare_triple (fun h => h = snd p)
                                                          (fst p)
                                                          Q).
  Proof.
    simplify.

    apply invariant_induction; simplify.

    propositional; subst; simplify.
    eapply HtConsequence.
    eassumption.
    equality.
    auto.

    eapply step_sound in H1.
    rewrite H2 in H1.
    auto.
  Qed.

  Theorem hoare_triple_sound : forall P {result} (c : cmd result) Q,
      hoare_triple P c Q
      -> forall h, P h
                   -> invariantFor (trsys_of c h)
                                   (fun p => step (fst p) (snd p) <> Failed).
  Proof.
    simplify.

    eapply invariant_weaken.
    eapply hoare_triple_sound'; eauto.
    simplify.
    eapply step_sound in H1.
    cases (step (fst s) (snd s)); equality.
  Qed.


  (** ** Showcasing the opportunity to create new programming abstractions,
       * without modifying the language definition *)

  (* Here's an example of a new programming construct defined within Gallina,
   * without extending the definition of object-language syntax.  It's for
   * folding a command over every one of the first [len] cells in memory.  We
   * work with some accumulator type [A], initializing the accumulator to [init]
   * and calling [combine] to update the accumulator for each value we read out
   * of memory. *)
  Definition heapfold {A : Set} (init : A) (combine : A -> nat -> cmd A) (len : nat) : cmd A :=
    p <- for p := (0, init) loop
           if len <=? fst p then
             Return (Done p)
           else
             h_i <- Read (fst p);
             acc <- combine (snd p) h_i;
             Return (Again (S (fst p), acc))
         done;
    Return (snd p).

  (* Next, two pretty mundane facts about list operations. *)

  Lemma firstn_nochange : forall A (ls : list A) n,
      length ls <= n
      -> firstn n ls = ls.
  Proof.
    induct ls; simplify.

    cases n; simplify; auto.

    cases n; simplify.
    linear_arithmetic.
    rewrite IHls; auto.
  Qed.

  Lemma fold_left_firstn : forall A B (f : A -> B -> A) (d : B) (ls : list B) (init : A) n,
      n < length ls
      -> f (fold_left f (firstn n ls) init) (nth_default d ls n)
         = fold_left f (firstn (S n) ls) init.
  Proof.
    induct ls; simplify.
    linear_arithmetic.
    cases n; simplify.
    unfold nth_default; simplify.
    reflexivity.
    rewrite <- IHls by linear_arithmetic.
    unfold nth_default; simplify.
    reflexivity.
  Qed.

  Hint Rewrite firstn_nochange fold_left_firstn using linear_arithmetic : core.

  (* Here's the soundness theorem for [heapfold], relying on a hypothesis of
   * soundness for [combine]. *)
  Theorem heapfold_ok : forall {A : Set} (init : A) combine
                               (ls : list nat) (f : A -> nat -> A),
    (forall P v acc,
      {{h ~> P h}}
        combine acc v
      {{r&h ~> r = f acc v /\ P h}})
    -> {{h ~> forall i, i < length ls -> h $! i = nth_default 0 ls i}}
         heapfold init combine (length ls)
       {{r&h ~> (forall i, i < length ls -> h $! i = nth_default 0 ls i)
           /\ r = fold_left f ls init}}.
  Proof.
    ht.
    loop_inv (fun r h => (forall i, i < length ls -> h $! i = nth_default 0 ls i)
                         /\ match r with
                            | Done (_, acc) => acc = fold_left f ls init
                            | Again (i, acc) => acc = fold_left f (firstn i ls) init
                            end).
    cases (length ls <=? a); ht; auto; simp; auto.
    rewrite H2 by assumption.
    simplify.
    reflexivity.
    simp; auto.
    simp.
  Qed.

  (* Here's a concrete use of [heapfold], to implement [array_max] more
   * succinctly. *)
  Definition array_max (len : nat) : cmd nat :=
    heapfold 0 (fun n m => Return (max n m)) len.

  (* Next, some more lemmas about lists and arithmetic *)

  Lemma le_max' : forall v ls acc,
      v <= acc
      -> v <= fold_left max ls acc.
  Proof.
    induct ls; simplify; auto.
  Qed.

  Lemma le_max : forall ls i acc,
      i < Datatypes.length ls
      -> nth_default 0 ls i <= fold_left max ls acc.
  Proof.
    induct ls; simplify.

    linear_arithmetic.

    cases i; simplify.
    unfold nth_default; simplify.
    apply le_max'; linear_arithmetic.
    unfold nth_default; simplify.
    apply IHls; linear_arithmetic.
  Qed.

  Hint Resolve le_max : core.

  (* Finally, a short proof of [array_max], appealing mostly to the generic
   * proof of [heapfold] *)
  Theorem array_max_ok : forall ls : list nat,
    {{ h ~> forall i, i < length ls -> h $! i = nth_default 0 ls i}}
      array_max (length ls)
    {{ r&h ~> forall i, i < length ls -> h $! i <= r }}.
  Proof.
    conseq.
    apply heapfold_ok with (f := max); ht.
    simp; auto.
    simp.
    rewrite H1 by assumption.
    auto.
  Qed.
End DeeperWithFail.

Extraction "DeeperWithFail.ml" DeeperWithFail.forever.
