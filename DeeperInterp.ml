open Deeper

let rec i2n n =
  match n with
  | 0 -> O
  | _ -> S (i2n (n - 1))

let interp c =
  let h : (nat, nat) Hashtbl.t = Hashtbl.create 0 in
  Hashtbl.add h (i2n 0) (i2n 2);
  Hashtbl.add h (i2n 1) (i2n 1);
  Hashtbl.add h (i2n 2) (i2n 8);
  Hashtbl.add h (i2n 3) (i2n 6);

  let rec interp' (c : 'a cmd) : 'a =
    match c with
    | Return v -> v
    | Bind (c1, c2) -> interp' (c2 (interp' c1))
    | Read a ->
      Obj.magic (try
                   Hashtbl.find h a
        with Not_found -> O)
    | Write (a, v) -> Obj.magic (Hashtbl.replace h a v)
    | Loop (i, b) ->
      match Obj.magic (interp' (Obj.magic (b i))) with
      | Done r -> r
      | Again r -> interp' (Loop (r, b))

  in h, interp' c
