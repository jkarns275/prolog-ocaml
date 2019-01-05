(** interned string *)
module IString =
  struct
    type t = int
    let compare a b = Pervasives.compare a b
  end

(** interned string, except it's a different type *)

type _varno_counter_t = { mutable n: int; } ;;
let _varno_counter = { n = 0; } ;;

let rec comma_separate strings =
  match strings with
  | [] -> ""
  | head :: [] -> head
  | head :: tail -> Printf.sprintf "%s, %s" head (comma_separate tail)


let rec args_to_string args (sb: IString.t -> string) =
  match args with
  | head :: [] -> head#to_string sb
  | head :: tail -> Printf.sprintf "%s, %s" (head#to_string sb) (args_to_string tail sb)
  | _ -> ""


type 'a var_t = { mutable instance: 'a option  }
and 'a term_kind =
  | Goal of int * 'a list
  | Var of int * 'a var_t
  | Atom
;;

class virtual term (name: IString.t) (kind: term term_kind) =
  object
    method name = name
    method get_kind = kind

    method virtual to_string : (IString.t -> string) -> string
    method virtual unify : term -> bool
    method virtual copy : term
    method virtual reset : unit
  end
;;

let trail =
  object (self)
    val mutable tr: term list = []
    val mutable len: int = 0

    method mark = len

    method push (t: term) =
      len <- len + 1;
      tr <- t :: tr

    method undo whereto  =
      match whereto with
      | 0 -> ()
      | _ ->
        match tr with
        | head :: tail ->
          tr <- tail;
          head#reset;
          self#undo (whereto - 1)
        | _ -> () (* This will never happen *)
  end
;;

class goal (name: IString.t) (args: term list) =
  object (self)
    inherit term name (Goal((List.length args), args))

    method args = args
    method name = name

    method to_string (sb: IString.t -> string) =
      let arg_strs = List.map (fun arg -> arg#to_string sb) args in
      let comma_separated_args = comma_separate arg_strs in
      Printf.sprintf "%s (%s)" (sb self#name) comma_separated_args

    method private unify_goals (self_args: term list) (other_args: term list) =
      match (self_args, other_args) with
      | [], [] -> true
      | [], h :: t -> false
      | h :: t, [] -> false
      | self_h :: self_t, other_h :: other_t ->
        if self_h#unify other_h then
          self#unify_goals self_t other_t
        else
          false

    method unify (other: term) =
      match other#get_kind with
      | Atom -> false
      | Goal (_len, other_args) ->
        if other#name = self#name then
          self#unify_goals args other_args
        else
          false
      | Var (varno, instance) ->
        match instance.instance with
        | Some inst -> self#unify inst
        | None ->
          trail#push other;
          instance.instance <- Some (self :> term);
          true

    method reset = ignore (List.map (fun ter -> ter#reset ) args)
    method copy = (new goal name (List.map (fun ter -> ter#copy ) args) :> term)

  end
;;

class var (name: IString.t) (varno: int) (instance: term var_t) =
  object (self)
    inherit term name (Var(varno, instance)) as super

    val instance: term var_t = instance
    val varno: int = 0

    method to_string (sb: IString.t -> string) =
      match instance.instance with
      | Some ter -> Printf.sprintf "%s = %s" (sb name) (ter#to_string sb)
      | None -> Printf.sprintf "%d@%s" varno (sb name)

    method unify (other: term) =
      match instance.instance with
      | None ->
        trail#push (self :> term);
        instance.instance <- Some other;
        true
      | Some ter -> other#unify (self :> term)

    method reset = instance.instance <- None

    method copy =
      let varno = _varno_counter.n in
      _varno_counter.n <- varno + 1;
      match instance.instance with
      | Some ter -> new var name varno { instance = (Some ter#copy); }
      | None -> new var name varno {instance = None; }
  end
;;

let make_var name inst =
  let varno = _varno_counter.n in
  _varno_counter.n <- varno + 1;
  new var name varno { instance = inst; }
;;

class atom (name: IString.t) =
  object (self)
    inherit term name Atom as super

    method to_string (sb: IString.t -> string) = Printf.sprintf ":%s" (sb name)
    method unify (other: term) =
      match self#get_kind with
      | Atom -> other#name = name
      | Var (varno, instance) -> true
      | _ -> true
    method copy = (self :> term)
    method reset = ()
  end
;;

type body = Goal of goal * body | Nil ;;
type rule = goal * body ;;

let rec append_to_body (lhs: body) (rhs: body) =
  match lhs with
  | Goal (goal, body) -> Goal(goal, append_to_body body rhs)
  | Nil -> rhs

module IStringMap = Map.Make(IString) ;;

type program = rule list IStringMap.t ;;

type clause_state = term option IStringMap.t ;;

type solver_state_t =
  {
    mutable program: program;
    mutable found_match: bool;
    mutable query: goal;
    sb: (IString.t -> string);
  } ;;

let fake_sb a = Printf.sprintf "~%d" a
let solver_state =
  {
    program = IStringMap.empty;
    found_match = false;
    query = new goal 0 [];
    sb = fake_sb;
  } ;;

let print_soln () = Printf.printf "%s\n" (solver_state.query#to_string fake_sb) ;;

let rec strip_clause_state (cl: goal) =
  strip_clause_state_inner cl#args (IStringMap. empty)
and strip_clause_state_inner (args: term list) (state: clause_state) =
  match args with
  | [] -> state
  | h :: tail ->
    match h#get_kind with
    | Var (varno, instance) ->
      let i = instance.instance in
      instance.instance <- None;
      strip_clause_state_inner tail IStringMap. (add varno i state)
    | _ -> strip_clause_state_inner tail state
;;

let rec resume_clause_state (cl: goal) (state: clause_state) =
  resume_clause_state_inner cl#args state
and resume_clause_state_inner (args: term list) (state: clause_state) =
  match args with
  | [] -> state
  | h :: tail ->
    match h#get_kind with
    | Var (varno, instance) ->
      instance.instance <- IStringMap.find varno state;
      resume_clause_state_inner tail state
    | _ -> resume_clause_state_inner tail state
;;

let rec try_unify_rule ((cl, rule_goals): rule) (goals: body) =
  let t = trail#mark in
  let clause_state = strip_clause_state cl in
  let res = match goals with
  | Nil -> false
  | Goal (g, goals_trail) ->
    if g#unify (cl :> term) then
      let unified_rules =
        match rule_goals with
        | Nil -> goals_trail
        | Goal (g, tail) -> append_to_body goals_trail rule_goals
      in
      match unified_rules with
      | Nil ->
        solver_state.found_match <- true;
        print_soln ();
        true
      | Goal (g, tail) -> solve_inner unified_rules
    else
      false
  in
  ignore (trail#undo t);
  ignore (resume_clause_state cl clause_state);
  res

and solve_inner (goals: body) =
  match goals with
  | Nil -> true
  | Goal (head, tail) ->
    match IStringMap. find_opt head#name solver_state.program with
    | None -> false
    | Some rules ->
      ignore (List.map (fun x -> try_unify_rule x goals) rules);
      true
;;

let solve (g: goal) =
  solver_state.query <- g;
  solve_inner (Goal(g, Nil))
;;
let test x y = (new goal x [new atom y], Nil) ;;
let q = test 0 6 ;;
solver_state.program <- IStringMap. (empty) ;;
solver_state.program <- IStringMap. (add 0 [q] solver_state.program) ;;
let q = new goal 0 [make_var 3 None] ;;
solve q;;

(* class query (query_goal: goal list) =
  object (self)
    val mutable found_match = false

    method solve =
      found_match <- false;
      current_query.query <- self;
      self#solve_inner 0

    method solve_inner (level: int) =
      match Program.find_opt query_goal#name program.p with
      | Some rules -> true
      | None -> false
  end
;;
*)
