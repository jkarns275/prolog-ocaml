type 'a vec_state =
  {
    mutable arr: 'a option array ;
    mutable size: int     ;
    mutable index: int    ;
  }
;;

let empty (n: int) (default: 'a) = { arr = Array.make n (Some default); size = n; index = 0; }

let expand_check (vs: 'a vec_state) =
  match vs.size, vs.index with
  | 0, 0 ->
    vs.arr <- Array.make 16 None;
    vs.size <- 16;
    ()
  | x, y ->
    if x = y then
      let new_arr = Array.make (2 * vs.size) None in
      Array.iteri (fun i el -> Array.set new_arr i el) vs.arr;
      vs.arr <- new_arr;
      vs.size <- 2 * vs.size;
      ()
    else
      ()

let append (it: 'a) (vs: 'a vec_state) =
  expand_check vs;
  Array.set vs.arr vs.index (Some it);
  vs.index <- vs.index + 1;
  ()

let get (i: int) (vs: 'a vec_state) = Array.get vs.arr i
