open Vec

module IString =
  struct
    type t = int
    let compare a b = Pervasives.compare a b
  end

module IStringMap = Map.Make(IString)
module StringMap = Map.Make(String)

type interner_state_t = { mutable s2i: IString.t StringMap.t; i2s: string vec; }

let interner_state = { s2i = StringMap.empty; i2s = Vec.empty () }


let intern (s: string) =
  match StringMap. find_opt s interner_state.s2i with
  | Some i -> i
  | None ->
    let i = Vec.length interner_state.i2s in
    interner_state.s2i <- StringMap. (add s i interner_state.s2i);
    Vec.append s interner_state.i2s;
    i
let get_string (i: IString.t) = Vec.get i interner_state.i2s
