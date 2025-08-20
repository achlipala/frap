Require Import Frap.
From Stdlib Require Import Program.


(** * Some data fodder for us to compute with later *)

(* Records are a handy way to define datatypes in terms of the named fields that
 * each value must contain. *)
Record programming_language := {
  Name : string;
  PurelyFunctional : bool;
  AppearedInYear : nat
}.

(* Here's a quick example of a set of programming languages, which we will use
 * below in some example computations. *)

Definition pascal := {|
  Name := "Pascal";
  PurelyFunctional := false;
  AppearedInYear := 1970
|}.

Definition clang := {|
  Name := "C";
  PurelyFunctional := false;
  AppearedInYear := 1972
|}.

Definition gallina := {|
  Name := "Gallina";
  PurelyFunctional := true;
  AppearedInYear := 1989
|}.

Definition haskell := {|
  Name := "Haskell";
  PurelyFunctional := true;
  AppearedInYear := 1990
|}.

Definition ocaml := {|
  Name := "OCaml";
  PurelyFunctional := false;
  AppearedInYear := 1996
|}.

Definition languages := [pascal; clang; gallina; haskell; ocaml].


(** * Classic list functions *)

(* The trio of "map/filter/reduce" are commonly presented as workhorse
 * *higher-order functions* for lists.  That is, they are functions that take
 * functions as arguments. *)

(* [map] runs a function on every position of a list to make a new list. *)
Fixpoint map {A B} (f : A -> B) (ls : list A) : list B :=
  match ls with
  | nil => nil
  | x :: ls' => f x :: map f ls'
  end.

Compute map (fun n => n + 2) [1; 3; 8].
(* Note the use of an *anonymous function* above via [fun]. *)

(* [filter] keeps only those elements of a list that pass a Boolean test. *)
Fixpoint filter {A} (f : A -> bool) (ls : list A) : list A :=
  match ls with
  | nil => nil
  | x :: ls' => if f x then x :: filter f ls' else filter f ls'
  end.

Compute filter (fun n => if n <=? 3 then true else false) [1; 3; 8].
(* The [if ... then true else false] bit might seem wasteful.  Actually, the
 * [<=?] operator has a fancy type that needs converting to [bool].  We'll get
 * more specific about such types in a future class. *)

(* [fold_left], a relative of "reduce," repeatedly applies a function to all
 * elements of a list. *)
Fixpoint fold_left {A B} (f : B -> A -> B) (ls : list A) (acc : B) : B :=
  match ls with
  | nil => acc
  | x :: ls' => fold_left f ls' (f acc x)
  end.

Compute fold_left max [1; 3; 8] 0.

(* Another way to see [fold_left] in action: *)
Theorem fold_left3 : forall {A B} (f : B -> A -> B) (x y z : A) (acc : B),
    fold_left f [x; y; z] acc = f (f (f acc x) y) z.
Proof.
  simplify.
  equality.
Qed.

(* Let's use these classics to implement a few simple "database queries" on the
 * list of programming languages.  Note that each field name from
 * [programming_language] is itself a first-class function, for projecting that
 * field from any record! *)

Compute map Name languages.
(* names of languages *)

Compute map Name (filter PurelyFunctional languages).
(* names of purely functional languages *)

Compute fold_left max (map AppearedInYear languages) 0.
(* maximum year in which a language appeared *)

Compute fold_left max (map AppearedInYear (filter PurelyFunctional languages)) 0.
(* maximum year in which a purely functional language appeared *)

(* To avoid confusing things, we'll revert to the standard library's (identical)
 * versions of these functions for the remainder. *)
Reset map.


(** * Sorting, parameterized in a comparison operation *)

Fixpoint insertion_sort {A} (le : A -> A -> bool) (ls : list A) : list A.
Admitted.

Fixpoint sorted {A} (le : A -> A -> bool) (ls : list A) : bool :=
  match ls with
  | [] => true
  | x1 :: ls' =>
    match ls' with
    | x2 :: _ => le x1 x2 && sorted le ls'
    | [] => true
    end
  end.

(* Main theorem: [insertion_sort] produces only sorted lists. *)
Theorem insertion_sort_sorted : forall {A} (le : A -> A -> bool),
    forall ls,
      sorted le (insertion_sort le ls) = true.
Proof.
Admitted.

(* Let's do a quick example of using [insertion_sort] with a concrete
 * comparator. *)

Definition not_introduced_later (l1 l2 : programming_language) : bool :=
  if AppearedInYear l1 <=? AppearedInYear l2 then true else false.

Compute insertion_sort
        not_introduced_later
        [gallina; pascal; clang; ocaml; haskell].

Corollary insertion_sort_languages : forall langs,
    sorted not_introduced_later (insertion_sort not_introduced_later langs) = true.
Proof.
Admitted.


(** * A language of functions and its interpreter *)

Inductive dyn :=
| Bool (b : bool)
| Number (n : nat)
| List (ds : list dyn).

Definition dmap (f : dyn -> dyn) (x : dyn) : dyn :=
  match x with
  | List ds => List (map f ds)
  | _ => x
  end.

Definition dfilter (f : dyn -> dyn) (x : dyn) : dyn :=
  match x with
    List ds => List (filter (fun arg => match f arg with
                                        | Bool b => b
                                        | _ => false
                                        end) ds)
  | _ => x
  end.

Definition disZero (x : dyn) : dyn :=
  match x with
  | Number 0 => Bool true
  | Number _ => Bool false
  | _ => x
  end.

Definition dnot (x : dyn) : dyn :=
  match x with
  | Bool b => Bool (negb b)
  | x => x
  end.

Inductive xform :=
| Identity
| Compose (xf1 xf2 : xform)
| Map (xf1 : xform)
| Filter (xf1 : xform)

| ConstantBool (b : bool)
| ConstantNumber (n : nat)
| IsZero
| Not.

Fixpoint transform (xf : xform) : dyn -> dyn :=
  match xf with
  | Identity => id
  | Compose f1 f2 => compose (transform f1) (transform f2)
  | Map f => dmap (transform f)
  | Filter f => dfilter (transform f)

  | ConstantBool b => fun _ => Bool b
  | ConstantNumber n => fun _ => Number n
  | IsZero => disZero
  | Not => dnot
  end.

Compute transform (Map IsZero) (List [Number 0; Number 1; Number 2; Number 0; Number 3]).
Compute transform (Filter IsZero) (List [Number 0; Number 1; Number 2; Number 0; Number 3]).

Fixpoint optimize (xf : xform) : xform.
Admitted.

Theorem optimize_ok : forall xf x, transform (optimize xf) x = transform xf x.
Proof.
Admitted.

(** ** Are these really optimizations?  Can they ever grow a term's size? *)

Fixpoint size (xf : xform) : nat :=
  match xf with
  | Identity
  | Not
  | IsZero
  | ConstantBool _
  | ConstantNumber _ => 1

  | Compose xf1 xf2 => 1 + size xf1 + size xf2
  | Map xf
  | Filter xf => 1 + size xf
  end.

Theorem optimize_optimizes : forall xf, size (optimize xf) <= size xf.
Proof.
Admitted.

(** ** More interestingly, the same is true of the action of these
       transformations on concrete values! *)

Fixpoint sum (ls : list nat) : nat :=
  match ls with
  | nil => 0
  | x :: ls' => x + sum ls'
  end.

Fixpoint dsize (d : dyn) : nat :=
  match d with
  | Bool _
  | Number _ => 1
  | List ds => 1 + sum (map dsize ds)
  end.

Theorem neverGrow : forall xf x,
    dsize (transform xf x) <= dsize x.
Proof.
Admitted.


(** * Combinators for syntax-tree transformations *)

(* Let's reprise the imperative language from the end of Interpreters. *)

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Definition valuation := fmap var nat.

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| Repeat (e : arith) (body : cmd).

Fixpoint selfCompose {A} (f : A -> A) (n : nat) : A -> A :=
  match n with
  | O => fun x => x
  | S n' => fun x => selfCompose f n' (f x)
  end.

Lemma selfCompose_extensional : forall {A} (f g : A -> A) n x,
  (forall y, f y = g y)
  -> selfCompose f n x = selfCompose g n x.
Proof.
  induct n; simplify; try equality.

  rewrite H.
  apply IHn.
  trivial.
Qed.

Fixpoint exec (c : cmd) (v : valuation) : valuation :=
  match c with
  | Skip => v
  | Assign x e => v $+ (x, interp e v)
  | Sequence c1 c2 => exec c2 (exec c1 v)
  | Repeat e body => selfCompose (exec body) (interp e v) v
  end.

Fixpoint seqself (c : cmd) (n : nat) : cmd :=
  match n with
  | O => Skip
  | S n' => Sequence c (seqself c n')
  end.

(* Now consider a more abstract way of describing optimizations concisely. *)

Record rule := {
  OnCommand : cmd -> cmd;
  OnExpression : arith -> arith
}.

Fixpoint bottomUp (r : rule) (c : cmd) : cmd :=
  match c with
  | Skip => r.(OnCommand) Skip
  | Assign x e => r.(OnCommand) (Assign x (r.(OnExpression) e))
  | Sequence c1 c2 => r.(OnCommand) (Sequence (bottomUp r c1) (bottomUp r c2))
  | Repeat e body => r.(OnCommand) (Repeat (r.(OnExpression) e) (bottomUp r body))
  end.

Definition crule (f : cmd -> cmd) : rule :=
  {| OnCommand := f; OnExpression := fun e => e |}.
Definition erule (f : arith -> arith) : rule :=
  {| OnCommand := fun c => c; OnExpression := f |}.
Definition andThen (r1 r2 : rule) : rule.
Admitted.

Definition plus0 := erule (fun e =>
                             match e with
                             | Plus e' (Const 0) => e'
                             | _ => e
                             end).
Definition unrollLoops := crule (fun c =>
                                   match c with
                                   | Repeat (Const n) body => seqself body n
                                   | _ => c
                                   end).

Compute bottomUp plus0
        (Sequence (Assign "x" (Plus (Var "x") (Const 0)))
                  (Assign "y" (Var "x"))).

Compute bottomUp unrollLoops
        (Repeat (Plus (Const 2) (Const 0))
                (Sequence (Assign "x" (Plus (Var "x") (Const 0)))
                          (Assign "y" (Var "x")))).

Compute bottomUp (andThen plus0 unrollLoops)
        (Repeat (Plus (Const 2) (Const 0))
                (Sequence (Assign "x" (Plus (Var "x") (Const 0)))
                          (Assign "y" (Var "x")))).

Definition correct (r : rule) : Prop.
Admitted.

Theorem crule_correct : forall f,
    (forall c v, exec (f c) v = exec c v)
    -> correct (crule f).
Proof.
Admitted.

Theorem erule_correct : forall f,
    (forall e v, interp (f e) v = interp e v)
    -> correct (erule f).
Proof.
Admitted.

Theorem andThen_correct : forall r1 r2,
    correct r1
    -> correct r2
    -> correct (andThen r1 r2).
Proof.
Admitted.

Theorem bottomUp_correct : forall r,
    correct r
    -> forall c v, exec (bottomUp r c) v = exec c v.
Proof.
Admitted.

Definition rBottomUp (r : rule) : rule.
Admitted.

Theorem rBottomUp_correct : forall r,
    correct r
    -> correct (rBottomUp r).
Proof.
Admitted.

Definition zzz := Assign "x" (Plus (Plus (Plus (Var "x") (Const 0)) (Const 0)) (Const 0)).

Compute bottomUp plus0 zzz.
Compute bottomUp (rBottomUp plus0) zzz.
Compute bottomUp (rBottomUp (rBottomUp plus0)) zzz.
Compute bottomUp (rBottomUp (rBottomUp (rBottomUp plus0))) zzz.
       


(** * Motivating continuations with search problems *)

Fixpoint allSublists {A} (ls : list A) : list (list A) :=
  match ls with
  | [] => [[]]
  | x :: ls' =>
    let lss := allSublists ls' in
    lss ++ map (fun ls'' => x :: ls'') lss
  end.

Compute allSublists [1; 2; 3].

Definition sublistSummingTo (ns : list nat) (target : nat) : option (list nat) :=
  match filter (fun ns' => if sum ns' ==n target then true else false) (allSublists ns) with
  | ns' :: _ => Some ns'
  | [] => None
  end.

Compute sublistSummingTo [1; 2; 3] 6.
Compute sublistSummingTo [1; 2; 3] 5.
Compute sublistSummingTo [1; 2; 3] 7.

(* This function will be handy to generate some test cases. *)
Fixpoint countingDown (from : nat) :=
  match from with
  | O => []
  | S from' => from' :: countingDown from'
  end.

Compute countingDown 10.

(* This one is pretty slow!  There are quite a few sublists of
 * [countingDown 18], you know. *)
Time Compute sublistSummingTo (countingDown 18) 1.


(** * The classics in continuation-passing style *)

(* We can rewrite the classic list higher-order functions in
 * *continuation-passing style*, where they return answers by calling
 * continuations rather than just returning normally. *)
































(* And CPS versions of the additional functions used in our examples earlier *)
Definition NameK {R} (l : programming_language) (k : string -> R) : R :=
  k (Name l).
Definition PurelyFunctionalK {R} (l : programming_language) (k : bool -> R) : R :=
  k (PurelyFunctional l).
Definition AppearedInYearK {R} (l : programming_language) (k : nat -> R) : R :=
  k (AppearedInYear l).
Definition maxK {R} (n1 n2 : nat) (k : nat -> R) : R :=
  k (max n1 n2).

(* The examples from before give the same answers, when suitably translated. *)
(*
Compute mapK NameK languages (fun ls => ls).
Compute filterK PurelyFunctionalK languages (fun ls => mapK NameK ls (fun x => x)).
Compute mapK AppearedInYearK languages (fun ls => fold_leftK maxK ls 0 (fun x => x)).
Compute filterK PurelyFunctionalK languages
        (fun ls1 => mapK AppearedInYearK ls1
                         (fun ls2 => fold_leftK maxK ls2 0 (fun x => x))).

Theorem names_ok : forall langs,
    mapK NameK langs (fun ls => ls) = map Name langs.
Proof.
Admitted.

Theorem purenames_ok : forall langs,
    filterK PurelyFunctionalK langs (fun ls => mapK NameK ls (fun x => x))
    = map Name (filter PurelyFunctional langs).
Proof.
Admitted.

Theorem latest_ok : forall langs,
    mapK AppearedInYearK langs (fun ls => fold_leftK maxK ls 0 (fun x => x))
    = fold_left max (map AppearedInYear langs) 0.
Proof.
Admitted.

Theorem latestpure_ok : forall langs,
    filterK PurelyFunctionalK langs
            (fun ls1 => mapK AppearedInYearK ls1
                             (fun ls2 => fold_leftK maxK ls2 0 (fun x => x)))
    = fold_left max (map AppearedInYear (filter PurelyFunctional langs)) 0.
Proof.
Admitted.
*)


(** * Tree traversals *)

Inductive tree {A} :=
| Leaf
| Node (l : tree) (d : A) (r : tree).
Arguments tree : clear implicits.

Fixpoint flatten {A} (t : tree A) : list A :=
  match t with
  | Leaf => []
  | Node l d r => flatten l ++ d :: flatten r
  end.

Fixpoint big (n : nat) : tree nat :=
  match n with
  | O => Leaf
  | S n' => Node (big n') n Leaf
  end.

Compute big 3.

Time Compute length (flatten (big 5000)).





















(** * Proof of our motivating example *)

(* This theorem is quite intricate to get right.  At this point in the class, it
 * is not important to follow anything about this proof, really, but it's kinda
 * cool, once digested. *)

(*
Theorem allSublistsK_ok : forall {A B} (ls : list A) (failed : unit -> B) found,
    (* First, we describe what makes for a legit [found] continuation. *)
    (forall sol,
        (* For any solution we might ask it about,
         * either [found] is going to accept that solution,
         * returning the same answer no matter which failure continuation we
         * pass: *)
        (exists ans, (forall failed', found sol failed' = ans)
                     /\ ans <> failed tt)
          (* ...and, by the way, this answer is never the same as the failure
           * value (or we could get confused in case analysis). *)

        (* OR [found] is going to reject this solution, invoking its failure
         * continuation: *)
        \/ (forall failed', found sol failed' = failed' tt))

    (* Then we conclude a rather similar property for [allSublistsK]. *)
    ->
    (* Option 1: there is a correct answer [sol], for which [found] returns
     * [ans]. *)
    (exists sol ans, In sol (allSublists ls)
                     /\ (forall failed', found sol failed' = ans)
                     /\ allSublistsK ls failed found = ans
                     /\ ans <> failed tt)

    (* Option 2: there is no correct answer. *)
    \/ ((forall sol, In sol (allSublists ls)
                     -> forall failed', found sol failed' = failed' tt)
        /\ allSublistsK ls failed found = failed tt).
Proof.
  induct ls; simplify.

  specialize (H []).
  first_order.
  right.
  propositional.
  subst.
  trivial.
  trivial.

  assert (let found := (fun (sol : list A) (failed' : unit -> B) =>
     found sol (fun _ : unit => found (a :: sol) failed')) in
          (exists (sol : list A) (ans : B),
              In sol (allSublists ls) /\
              (forall failed' : unit -> B, found sol failed' = ans) /\
              allSublistsK ls failed found = ans /\ ans <> failed tt) \/
          (forall sol : list A,
              In sol (allSublists ls) -> forall failed' : unit -> B, found sol failed' = failed' tt) /\
          allSublistsK ls failed found = failed tt).
  apply IHls.
  first_order.
  generalize (H sol).
  first_order.
  specialize (H (a :: sol)).
  first_order.
  left.
  exists x; propositional.
  rewrite H0.
  trivial.
  right.
  simplify.
  rewrite H0.
  trivial.

  clear IHls.
  simplify.
  first_order.

  generalize (H x); first_order.
  left; exists x, x1; propositional.
  apply in_or_app; propositional.
  specialize (H1 failed).
  specialize (H4 (fun _ => found (a :: x) failed)).
  equality.
  left; exists (a :: x), x0; propositional.
  apply in_or_app; right; apply in_map_iff.
  first_order.
  specialize (H1 failed').
  rewrite H4 in H1.
  trivial.

  right; propositional.
  apply in_app_or in H2; propositional.

  generalize (H sol); first_order.
  apply H0 with (failed' := failed') in H3.
  rewrite H2 in H3.
  equality.

  apply in_map_iff in H3.
  first_order.
  subst.
  generalize (H x); first_order.
  apply H0 with (failed' := failed) in H3.
  equality.
  apply H0 with (failed' := failed') in H3.
  rewrite H2 in H3; trivial.
Qed.

(* At least we can wrap it all up in a simple correctness theorem! *)
Theorem sublistSummingToK_ok : forall ns target,
    match sublistSummingToK ns target with
    | None => forall sol, In sol (allSublists ns) -> sum sol <> target
    | Some sol => In sol (allSublists ns) /\ sum sol = target
    end.
Proof.
  simplify.
  unfold sublistSummingToK.
  pose proof (allSublistsK_ok ns (fun _ => None)
              (fun sol failed => if sum sol ==n target then Some sol else failed tt)).
  cases H.

  simplify.
  cases (sum sol ==n target).
  left; exists (Some sol); equality.
  propositional.

  first_order.
  specialize (H0 (fun _ => None)).
  cases (sum x ==n target); try equality.
  subst.
  rewrite H1.
  propositional.

  first_order.
  rewrite H0.
  simplify.
  apply H with (failed' := fun _ => None) in H1.
  cases (sum sol ==n target); equality.
Qed.
*)
