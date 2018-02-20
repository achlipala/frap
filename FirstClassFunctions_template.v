Require Import Frap.


(** * Some data fodder for us to compute with later *)

Record programming_language := {
  Name : string;
  PurelyFunctional : bool;
  AppearedInYear : nat
}.

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

Fixpoint map {A B} (f : A -> B) (ls : list A) : list B :=
  match ls with
  | nil => nil
  | x :: ls' => f x :: map f ls'
  end.

Compute map (fun n => n + 2) [1; 3; 8].

Fixpoint filter {A} (f : A -> bool) (ls : list A) : list A :=
  match ls with
  | nil => nil
  | x :: ls' => if f x then x :: filter f ls' else filter f ls'
  end.

Compute filter (fun n => if n <=? 3 then true else false) [1; 3; 8].

Fixpoint fold_left {A B} (f : B -> A -> B) (ls : list A) (acc : B) : B :=
  match ls with
  | nil => acc
  | x :: ls' => fold_left f ls' (f acc x)
  end.

Compute fold_left max [1; 3; 8] 0.

Theorem fold_left3 : forall {A B} (f : B -> A -> B) (x y z : A) (acc : B),
    fold_left f [x; y; z] acc = f (f (f acc x) y) z.
Proof.
  simplify.
  equality.
Qed.

Compute map Name languages.

Compute map Name (filter PurelyFunctional languages).

Compute fold_left max (map AppearedInYear languages) 0.

Compute fold_left max (map AppearedInYear (filter PurelyFunctional languages)) 0.

(* To avoid confusing things, we'll revert to the standard library's (identical)
 * versions of these functions for the remainder. *)
Reset map.


(** * Sorting, parameterized in a comparison operation *)

Fixpoint insert {A} (le : A -> A -> bool) (new : A) (ls : list A) : list A :=
  match ls with
  | [] => [new]
  | x :: ls' =>
    if le new x then
      new :: ls
    else
      x :: insert le new ls'
  end.

Fixpoint insertion_sort {A} (le : A -> A -> bool) (ls : list A) : list A :=
  match ls with
  | [] => []
  | x :: ls' => insert le x (insertion_sort le ls')
  end.

Fixpoint sorted {A} (le : A -> A -> bool) (ls : list A) : bool :=
  match ls with
  | [] => true
  | x1 :: ls' =>
    match ls' with
    | x2 :: _ => le x1 x2 && sorted le ls'
    | [] => true
    end
  end.

Theorem insertion_sort_sorted : forall {A} (le : A -> A -> bool) ls,
    sorted le (insertion_sort le ls) = true.
Proof.
Admitted.

Definition not_introduced_later (l1 l2 : programming_language) : bool :=
  if AppearedInYear l1 <=? AppearedInYear l2 then true else false.

Compute insertion_sort
        not_introduced_later
        [gallina; pascal; c; ocaml; haskell].

Corollary insertion_sort_languages : forall langs,
    sorted not_introduced_later (insertion_sort not_introduced_later langs) = true.
Proof.
Admitted.


(** * Motivating continuations with search problems *)

Fixpoint allSublists {A} (ls : list A) : list (list A) :=
  match ls with
  | [] => [[]]
  | x :: ls' =>
    let lss := allSublists ls' in
    lss ++ map (fun ls'' => x :: ls'') lss
  end.

Compute allSublists [1; 2; 3].

Definition sum ls := fold_left plus ls 0.

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
