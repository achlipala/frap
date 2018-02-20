(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Supplementary Coq material: first-class functions and continuations
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

(* Next stop in touring the basic Coq ingredients of functional programming and
 * proof: functions as first-class data.  These days, most trendy programming
 * languages contain this feature, though it can't hurt to review; and we'll see
 * patterns in specification and proof that are helpful to handle first-class
 * functions. *)


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

Definition c := {|
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

Definition languages := [pascal; c; gallina; haskell; ocaml].


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

(* Another classic family of higher-order functions is for sorting, where we
 * typically take a *comparator* as input.  Such a function helps us compare
 * data elements with each other.  Let's do insertion sort as an example. *)

(* Important helper function: take in an assumed-sorted list [ls]; generate a
 * new list that is like [ls] but with [new] inserted at the appropriate
 * position to maintain sortedness.  We use "less than or equal to" test [le] to
 * define sortedness. *)
Fixpoint insert {A} (le : A -> A -> bool) (new : A) (ls : list A) : list A :=
  match ls with
  | [] => [new]
  | x :: ls' =>
    if le new x then
      new :: ls
    else
      x :: insert le new ls'
  end.

(* Now insertion sort is just repeated use of [insert]. *)
Fixpoint insertion_sort {A} (le : A -> A -> bool) (ls : list A) : list A :=
  match ls with
  | [] => []
  | x :: ls' => insert le x (insertion_sort le ls')
  end.

(* To help us state our main theorem, we define sortedness. *)
Fixpoint sorted {A} (le : A -> A -> bool) (ls : list A) : bool :=
  match ls with
  | [] => true
  | x1 :: ls' =>
    match ls' with
    | x2 :: _ => le x1 x2 && sorted le ls'
    | [] => true
    end
  end.

(* [insert] preserves sortedness.  Note the crucial hypothesis that comaprator
 * [le] is *total*: any two elements are related by it, in one order or the
 * other. *)
Lemma insert_sorted : forall {A} (le : A -> A -> bool) a,
    (forall x y, le x y = false -> le y x = true)
    -> forall ls, sorted le ls = true
                  -> sorted le (insert le a ls) = true.
Proof.
  induct ls; simplify; trivial.

  cases (le a a0); simplify.

  rewrite Heq; simplify.
  trivial.

  cases ls; simplify.
  rewrite H; trivial.
  apply andb_true_iff in H0; propositional.
  cases (le a a1); simplify.
  apply andb_true_iff in H0; propositional.
  rewrite H; trivial.
  simplify.
  rewrite H3, H4; trivial.
  rewrite H1; simplify.
  trivial.
Qed.  

(* Main theorem: [insertion_sort] produces only sorted lists. *)
Theorem insertion_sort_sorted : forall {A} (le : A -> A -> bool),
    (forall x y, le x y = false -> le y x = true)
    -> forall ls,
      sorted le (insertion_sort le ls) = true.
Proof.
  induct ls; simplify; trivial.
  apply insert_sorted; trivial.
Qed.

(* The other classic requirement of a sorting function is that it return a
 * permutation of its input, but we will skip that element here, since it is
 * orthogonal to practicing with higher-order functions. *)

(* Let's do a quick example of using [insertion_sort] with a concrete
 * comparator. *)

Definition not_introduced_later (l1 l2 : programming_language) : bool :=
  if AppearedInYear l1 <=? AppearedInYear l2 then true else false.

Compute insertion_sort
        not_introduced_later
        [gallina; pascal; c; ocaml; haskell].

Corollary insertion_sort_languages : forall langs,
    sorted not_introduced_later (insertion_sort not_introduced_later langs) = true.
Proof.
  simplify.
  apply insertion_sort_sorted.
  unfold not_introduced_later.
  simplify.
  cases (AppearedInYear x <=? AppearedInYear y); try equality.
  cases (AppearedInYear y <=? AppearedInYear x); try equality.
  linear_arithmetic.
Qed.


(** * Motivating continuations with search problems *)

(* One fascinating flavor of first-class functions is *continuations*, which are
 * essentially functions that are meant to be called on the *results* of other
 * functions.  To motivate the idea, let's first develop a somewhat slow
 * function.  We'll switch to a continuation-based version to see the
 * benefit. *)

(* Here's a simple way to compute all lists that can be formed by dropping zero
 * or more elements out of some original list. *)
Fixpoint allSublists {A} (ls : list A) : list (list A) :=
  match ls with
  | [] => [[]]
  | x :: ls' =>
    let lss := allSublists ls' in
    lss ++ map (fun ls'' => x :: ls'') lss
  end.

Compute allSublists [1; 2; 3].

Definition sum ls := fold_left plus ls 0.

(* This is the main function we want to define.  It looks for a sublist whose
 * sum matches some target. *)
Fixpoint sublistSummingTo (ns : list nat) (target : nat) : option (list nat) :=
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

(* Can we set things up so that we can avoid generating *all* sublists, instead
 * checking each one for the right sum, as it is generated?  And can we do it in
 * a *generic* way, where we still have sublists calculation that isn't
 * specialized to any particular acceptance condition?  Continuations provide a
 * nice ingredient! *)

(* This variant of [allSublists] takes a while to digest.  Both of the new
 * arguments are continuations. *)
Fixpoint allSublistsK {A R} (ls : list A)
         (* First, notice new type parameter [R], for "result."
          * The function will return a value of this type. *)
         
         (failed : unit -> R)
         (* If no acceptable sublist is found, return the result of calling this
          * function.  [unit] is the degenerate standard-library type inhabited
          * only by [tt]. *)

         (found : list A -> (unit -> R) -> R)
         (* Whenever an acceptable sublist is found, return the result of
          * calling this function on it.  The 2nd argument is a failure
          * continuation, just like our own [failed].  That is, when [found]
          * "doesn't like" the list, it returns the result of calling the
          * function we pass to it.  See below for why this is a perfect
          * plumbing strategy. *)
         
  : R :=
  match ls with
  | [] =>
    found [] failed
    (* [ls] is empty?  Then the only sublist is [[]], which we should send to
     * our success continuation [found] for vetting. *)
  | x :: ls' =>
    (* [ls] is nonempty?  Let's proceed to finding all sublists of [ls']. *)
    allSublistsK ls'
                 failed
                 (* Any failure here bubbles up to a failure in the original
                  * call. *)
                 (fun sol failed' =>
                    (* Any success here should first be passed on to the
                     * original success continuation [found]. *)
                    found sol (fun _ =>
                                 (* However, if [found] doesn't like [sol], then
                                  * maybe it likes [x :: sol]!  Note how we
                                  * customize the failure continuation passed to
                                  * [found], to implement a kind of backtracking
                                  * search, interleaved with generation of
                                  * candidates. *)
                                 found (x :: sol) failed'))
  end.

(* Now it is easy to define a variant of [sublistSummingTo], where result type
 * [R] gets instantiated as [option (list nat)]. *)
Definition sublistSummingToK (ns : list nat) (target : nat) : option (list nat) :=
  allSublistsK ns
               (fun _ => None)
               (* Failure continuation: return None. *)
               (fun sol failed =>
                  if sum sol ==n target then Some sol else failed tt)
               (* Success continuation: check if sum is right, if so returning
                * [Some]. *).

Time Compute sublistSummingToK (countingDown 18) 1.
(* Significantly faster now!  We avoid materializing the full list of sublists,
 * before starting to filter them.  We will return below to proof of this
 * function, which is irksomely involved. *)


(** * The classics in continuation-passing style *)

(* We can rewrite the classic list higher-order functions in
 * *continuation-passing style*, where they return answers by calling
 * continuations rather than just returning normally.  This style might be
 * familiar from, e.g., how *asynchronous programming* works in JavaScript. *)

(* Notice how, not only does [mapK] have a CPS (continuation-passing style)
 * type, but its function argument also has a CPS type. *)
Fixpoint mapK {A B R} (f : A -> (B -> R) -> R) (ls : list A) (k : list B -> R) : R :=
  match ls with
  | nil => k nil
  | x :: ls' => f x (fun x' => mapK f ls' (fun ls'' => k (x' :: ls'')))
  end.

Fixpoint filterK {A R} (f : A -> (bool -> R) -> R) (ls : list A) (k : list A -> R) : R :=
  match ls with
  | nil => k nil
  | x :: ls' => f x (fun b => filterK f ls' (fun ls'' => k (if b then x :: ls'' else ls'')))
  end.

Fixpoint fold_leftK {A B R} (f : B -> A -> (B -> R) -> R) (ls : list A) (acc : B) (k : B -> R) : R :=
  match ls with
  | nil => k acc
  | x :: ls' => f acc x (fun x' => fold_leftK f ls' x' k)
  end.

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
Compute mapK NameK languages (fun ls => ls).
Compute filterK PurelyFunctionalK languages (fun ls => mapK NameK ls (fun x => x)).
Compute mapK AppearedInYearK languages (fun ls => fold_leftK maxK ls 0 (fun x => x)).
Compute filterK PurelyFunctionalK languages
        (fun ls1 => mapK AppearedInYearK ls1
                         (fun ls2 => fold_leftK maxK ls2 0 (fun x => x))).

(* We can prove that each such example always gives correct answers, for any
 * list of languages. *)
Theorem mapK_ok : forall {A B R} (f : A -> (B -> R) -> R) (f_base : A -> B),
    (forall x k, f x k = k (f_base x))
    -> forall (ls : list A) (k : list B -> R),
      mapK f ls k = k (map f_base ls).
Proof.
  induct ls; simplify; try equality.

  rewrite H.
  apply IHls.
Qed.

Theorem names_ok : forall langs,
    mapK NameK langs (fun ls => ls) = map Name langs.
Proof.
  simplify.
  apply mapK_ok with (f_base := Name).
  unfold NameK.
  trivial.
Qed.

Theorem filterK_ok : forall {A R} (f : A -> (bool -> R) -> R) (f_base : A -> bool),
    (forall x k, f x k = k (f_base x))
    -> forall (ls : list A) (k : list A -> R),
      filterK f ls k = k (filter f_base ls).
Proof.
  induct ls; simplify; try equality.

  rewrite H.
  apply IHls.
Qed.

Theorem purenames_ok : forall langs,
    filterK PurelyFunctionalK langs (fun ls => mapK NameK ls (fun x => x))
    = map Name (filter PurelyFunctional langs).
Proof.
  simplify.
  rewrite filterK_ok with (f_base := PurelyFunctional); trivial.
  apply mapK_ok with (f_base := Name); trivial.
Qed.

Theorem fold_leftK_ok : forall {A B R} (f : B -> A -> (B -> R) -> R) (f_base : B -> A -> B),
    (forall x acc k, f x acc k = k (f_base x acc))
    -> forall (ls : list A) (acc : B) (k : B -> R),
      fold_leftK f ls acc k = k (fold_left f_base ls acc).
Proof.
  induct ls; simplify; try equality.

  rewrite H.
  apply IHls.
Qed.

Theorem latest_ok : forall langs,
    mapK AppearedInYearK langs (fun ls => fold_leftK maxK ls 0 (fun x => x))
    = fold_left max (map AppearedInYear langs) 0.
Proof.
  simplify.
  rewrite mapK_ok with (f_base := AppearedInYear); trivial.
  apply fold_leftK_ok with (f_base := max); trivial.
Qed.

Theorem latestpure_ok : forall langs,
    filterK PurelyFunctionalK langs
            (fun ls1 => mapK AppearedInYearK ls1
                             (fun ls2 => fold_leftK maxK ls2 0 (fun x => x)))
    = fold_left max (map AppearedInYear (filter PurelyFunctional langs)) 0.
Proof.
  simplify.
  rewrite filterK_ok with (f_base := PurelyFunctional); trivial.
  rewrite mapK_ok with (f_base := AppearedInYear); trivial.
  apply fold_leftK_ok with (f_base := max); trivial.
Qed.


(** * Tree traversals *)

(* Let's see how the way of continuations can guide us toward defining a tree
 * traversal as a "loop" rather than a general recursive function. *)

(* Recall this type from last week. *)
Inductive tree {A} :=
| Leaf
| Node (l : tree) (d : A) (r : tree).
Arguments tree : clear implicits.

(* And here's an in-order traversal that we also already worked with. *)
Fixpoint flatten {A} (t : tree A) : list A :=
  match t with
  | Leaf => []
  | Node l d r => flatten l ++ d :: flatten r
  end.

(* This flattening does some wasteful extra copying-around of list elements,
 * with all those [++] operations.  We can surface the quadratic running time
 * with large enough test cases. *)

Fixpoint big (n : nat) : tree nat :=
  match n with
  | O => Leaf
  | S n' => Node (big n') n Leaf
  end.

Compute big 3.

Time Compute length (flatten (big 5000)).
(* That one takes long enough to notice (and larger trees lead to stack
 * overflows!). *)

(* Let's write a version that avoids repeated list concatenation, by maintaining
 * an *accumulator*, where we "accumulate" the answer is reverse order. *)
Fixpoint flattenAcc {A} (t : tree A) (acc : list A) : list A :=
  match t with
  | Leaf => acc
  | Node l d r => flattenAcc l (d :: flattenAcc r acc)
  end.

(* It gives the same answer as the original. *)
Theorem flattenAcc_ok : forall {A} (t : tree A) acc,
    flattenAcc t acc = flatten t ++ acc.
Proof.
  induct t; simplify; try equality.

  rewrite IHt1, IHt2.
  rewrite <- app_assoc.
  simplify.
  equality.
Qed.

Time Compute length (flattenAcc (big 5000) []).
(* Much faster! *)

(* There is a generic transformation of any function into CPS.  We won't spell
 * the transformation out formally, but here's what it does for [flattenAcc]. *)
Fixpoint flattenK {A R} (t : tree A) (acc : list A) (k : list A -> R) : R :=
  match t with
  | Leaf => k acc
  | Node l d r => flattenK r acc (fun acc' =>
                                    flattenK l (d :: acc') k)
  end.
(* Note how the first recursive call takes as an argument a continuation that
 * makes a further recursive call.  We have made all recursive calls into tail
 * calls, which wasn't true in the original function. *)

(* This version is still correct. *)
Theorem flattenK_ok : forall {A R} (t : tree A) acc (k : list A -> R),
    flattenK t acc k = k (flattenAcc t acc).
Proof.
  induct t; simplify; try equality.

  rewrite IHt2, IHt1.
  equality.
Qed.

(* Continuations can feel something like magic.  Let's concretize them by
 * replacing them with a datatype that doesn't appeal to first-class functions.
 * This kind of transformation is called *defunctionalization*, and it can also
 * be done quite mechanically. *)
Inductive flatten_continuation {A} :=
| KDone
  (* This is a base-case identity function, which we might use to kick off the
   * recursion for [flattenK]. *)
| KMore (l : tree A) (d : A) (k : flatten_continuation)
  (* For given arguments [l d k], this one corresponds to:
   * [fun acc' => flattenK l (d :: acc') k] *).
Arguments flatten_continuation : clear implicits.

(* This function explains how to apply one of our defunctionalized continuations
 * to an accumulator.  We also need to take the new flattening function as an
 * argument. *)
Definition apply_continuation {A} (acc : list A) (k : flatten_continuation A)
         (flattenKD : tree A -> list A -> flatten_continuation A -> list A)
         : list A :=
  match k with
  | KDone => acc
  | KMore l d k' => flattenKD l (d :: acc) k'
                    (* Note how this case just copies back in the code that
                     * inspired our inclusion of the constructor [KMore]. *)
  end.

(* Here's the overall function.  Note a pesky element: we add an extra [nat]
 * parameter of *fuel*, a count that goes down across recursive calls, just to
 * convince Coq that our function terminates.  Otherwise, the recursion
 * structure is too intricate for Coq to make sense of. *)
Fixpoint flattenKD {A} (fuel : nat) (t : tree A) (acc : list A)
         (k : flatten_continuation A) : list A :=
  match fuel with
  | O => []
  | S fuel' =>
    match t with
    | Leaf => apply_continuation acc k (flattenKD fuel')
              (* Note the partial
               * application of [flattenKD]. --^ *)
    | Node l d r => flattenKD fuel' r acc (KMore l d k)
    end
  end.
(* Now, again, all function calls are tail calls, but we also don't rely on
 * first-class functions. *)

(* Next, to prove correctness, we will need good notions of sizes of things, to
 * tell us how much fuel is needed. *)

(* A somewhat peculiar notion of size for trees.  Why that 2 instead of 1?
 * Because it lets the proof below work out! *)
Fixpoint size {A} (t : tree A) : nat :=
  match t with
  | Leaf => 0
  | Node l _ r => 2 + size l + size r
  end.

Fixpoint continuation_size {A} (k : flatten_continuation A) : nat :=
  match k with
  | KDone => 0
  | KMore l d k' => 1 + size l + continuation_size k'
  end.

(* A continuation encodes a flattening call, waiting to be run.
 * We can go ahead and run all of it, using the original, simple [flatten]. *)
Fixpoint flatten_cont {A} (k : flatten_continuation A) : list A :=
  match k with
  | KDone => []
  | KMore l d k' => flatten_cont k' ++ flatten l ++ [d]
  end.

(* That operation turns out to be just what we need to state correctness.
 * We also have to fiddle with fuel, effectively building in a kind of
 * *strong induction* via the parameter [fuel], which bounds the actual fuel
 * amount [fuel']. *)
Lemma flattenKD_ok' : forall {A} fuel fuel' (t : tree A) acc k,
    size t + continuation_size k < fuel' < fuel
    -> flattenKD fuel' t acc k
       = flatten_cont k ++ flatten t ++ acc.
Proof.
  induct fuel; simplify; cases fuel'; simplify; try linear_arithmetic.

  cases t; simplify; trivial.

  cases k; simplify; trivial.
  rewrite IHfuel; try linear_arithmetic.
  repeat rewrite <- app_assoc.
  simplify.
  equality.

  rewrite IHfuel.
  simplify.
  repeat rewrite <- app_assoc.
  simplify.
  equality.
  simplify.
  linear_arithmetic.
Qed.

(* A nice, simple final theorem can be stated, when we initialize fuel in the
 * right way. *)
Theorem flattenKD_ok : forall {A} (t : tree A),
    flattenKD (size t + 1) t [] KDone = flatten t.
Proof.
  simplify.
  rewrite flattenKD_ok' with (fuel := size t + 2).
  simplify.
  apply app_nil_r.
  simplify.
  linear_arithmetic.
Qed.

(* The author was once asked a programming interview question, of how to perform
 * some tree traversal with a loop but not recursion.  Our last step shows how
 * to do that for flattening, just relying on explicit lists that effectively
 * represent call stacks!  Actually, such data have been implicit in our
 * defunctionalized continuations. *)

(* Specifically, one of our continuations is really just a list of arguments to
 * pending calls to [flatten]. *)
Definition call_stack A := list (tree A * A).

(* This analogue to [apply_continuation] explains how to "pop the current stack
 * frame" and return to the most recent suspended call. *)
Definition pop_call_stack {A} (acc : list A) (st : call_stack A)
         (flattenS : tree A -> list A -> call_stack A -> list A)
         : list A :=
  match st with
  | [] => acc
  | (l, d) :: st' => flattenS l (d :: acc) st'
  end.

(* And here's the rewritten main function. *)
Fixpoint flattenS {A} (fuel : nat) (t : tree A) (acc : list A)
         (st : call_stack A) : list A :=
  match fuel with
  | O => []
  | S fuel' =>
    match t with
    | Leaf => pop_call_stack acc st (flattenS fuel')
    | Node l d r => flattenS fuel' r acc ((l, d) :: st)
    end
  end.

(* To prove correctness, we will want a translation from the new kind of
 * continuation to the old. *)
Fixpoint call_stack_to_continuation {A} (st : call_stack A) : flatten_continuation A :=
  match st with
  | [] => KDone
  | (l, d) :: st' => KMore l d (call_stack_to_continuation st')
  end.

Lemma flattenS_flattenKD : forall {A} fuel (t : tree A) acc st,
    flattenS fuel t acc st = flattenKD fuel t acc (call_stack_to_continuation st).
Proof.
  induct fuel; simplify; trivial.

  cases t.

  cases st; simplify; trivial.
  cases p; simplify.
  apply IHfuel.

  apply IHfuel.
Qed.

Theorem flattenS_ok : forall {A} (t : tree A),
    flattenS (size t + 1) t [] [] = flatten t.
Proof.
  simplify.
  rewrite flattenS_flattenKD.
  apply flattenKD_ok.
Qed.


(** * Proof of our motivating example *)

(* This theorem is quite intricate to get right.  At this point in the class, it
 * is not important to follow anything about this proof, really, but it's kinda
 * cool, once digested. *)

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
