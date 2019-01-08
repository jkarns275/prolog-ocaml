open Interner

let rec comma_separate strings =
  match strings with
  | [] -> ""
  | head :: [] -> head
  | head :: tail -> Printf.sprintf "%s, %s" head (comma_separate tail)

module Term =
  struct

    type _varno_counter_t = { mutable n: int; }
    let _varno_counter = { n = 0; }

    type var_t = { mutable instance: t option;  }
    and tail_t = { mutable tail: term_list option; }
    and term_list =
      | TList of t * term_list
      | Tail of tail_t
      | Nil
    and kind =
      | Var of int * var_t
      | List of term_list
      | Atom
    and t = IString.t * kind

    let rec map_term_list f tl =
      match tl with
      | TList (term, tail) -> (f term) :: map_term_list f tail
      | Nil -> []
      | Tail t ->
        match t.tail with
        | Some tail -> map_term_list f tail
        | None -> []

    let make_atom (is: string) = (Interner.intern is), Atom

    let rec make_list (terms: t list) =
      match terms with
      | [] -> Nil
      | term :: tail -> TList (term, make_list tail)
    let rec make_list_with_tail_inner (terms: t list) (tail: tail_t) =
      match terms with
      | [] -> Tail tail
      | term :: t -> TList (term, make_list_with_tail_inner t tail)
    and make_list_with_tail (name: IString.t) (terms: t list) (tail: tail_t) =
      name, List (make_list_with_tail_inner terms tail)

    let rec make_var_internal name inst =
      let varno = _varno_counter.n in
      _varno_counter.n <- varno + 1;
      name, varno, { instance = inst; }
    and make_var name inst =
      let (name, varno, vt) = make_var_internal name inst in
      name, Var (varno, vt)

    let make_tail (tail: term_list option) = { tail; }

    let rec copy_term_list tl =
      match tl with
      | TList (term, tail) -> TList (copy term, copy_term_list tail)
      | Nil -> Nil
      | Tail tt -> Tail (make_tail tt.tail)
    and copy_var name varno vt =
      match vt.instance with
        | Some i -> make_var_internal name (Some (copy i))
        | None -> make_var_internal name None
    and copy ((name, kind): t) =
      match kind with
      | Var (varno, vt) ->
        let (name, varno, vt) = copy_var name varno vt in
        name, Var (varno, vt)
      | Atom -> name, kind
      | List l -> name, List (copy_term_list l)

    let rec reset ((name, kind): t) =
      match kind with
      | Var (varno, inst) ->
        inst.instance <- None;
        ()
      | List l -> ignore (map_term_list (fun term -> reset term) l)
      | Atom -> ()

    let rec string_of_term_list (tl: term_list) = Printf.sprintf "[%s]" (string_of_term_list_inner tl)
    and string_of_term_list_inner (tl: term_list) =
      match tl with
      | TList (term, tail) -> (
        match tail with
        | Nil -> Printf.sprintf "%s" (string_of_term term)
        | Tail t -> (
          match t.tail with
          | None -> Printf.sprintf "%s | Tail" (string_of_term term)
          | Some tail -> Printf.sprintf "%s, %s" (string_of_term term) (string_of_term_list_inner tail)
        )
        | TList _ -> Printf.sprintf "%s, %s" (string_of_term term) (string_of_term_list_inner tail)
      )
      | Nil -> ""
      | Tail t -> "" (* This is uncreachable *)
    and string_of_term ((name, kind): t) =
      match kind with
      | List l -> string_of_term_list l
      | Atom -> Interner.get_string name
      | Var (varno, inst) ->
        match inst.instance with
        | Some x -> string_of_term x
        | None -> Printf.sprintf "%d%s" varno (Interner.get_string name)

    let trail =
      object (self)
        val mutable tr: t list = []
        val mutable len: int = 0

        method mark = len

        method push (t: t) =
          len <- len + 1;
          tr <- t :: tr

        method undo whereto  =
          if whereto = len then
            ()
          else
            match tr with
            | head :: tail ->
              len <- len - 1;
              tr <- tail;
              reset head;
              self#undo whereto
            | _ -> () (* This will never happen *)
      end

    let rec unify_lists (l0: term_list) (l1: term_list) =
      match l0, l1 with
      | TList (t0, tail0), TList (t1, tail1) ->
        if unify t0 t1 then unify_lists tail0 tail1 else false
      | Nil, Tail t -> unify_lists l1 l0
      | Tail t, Nil -> (
        match t.tail with
        | Some tail -> false
        | None -> true
      )
      | TList (t0, tail), Tail t1 -> unify_lists l1 l0
      | Tail t0, TList (t1, tail) -> (
        match t0.tail with
        | Some t -> unify_lists t tail
        | None ->
          t0.tail <- Some l1;
          trail#push (0, List l0);
          true
      )
      | Tail t0, Tail t1 -> (
        match t0.tail, t1.tail with
        | Some tail0, Some tail1 -> unify_lists tail0 tail1
        | Some tail0, None ->
          t1.tail <- Some tail0;
          trail#push (0, List l1);
          true
        | None, Some tail1 ->
          t0.tail <- Some tail1;
          trail#push (0, List l0);
          true
        | None, None ->
          t0.tail <- Some l1;
          trail#push (0, List l0);
          true
      )
      | TList _, Nil -> false
      | Nil, TList _ -> false
      | Nil, Nil -> true

    and unify (t0: t) (t1: t) =
      let n0, k0 = t0 in
      let n1, k1 = t1 in
      match k0, k1 with
      | List l0, List l1 -> unify_lists l0 l1
      | List l0, Atom -> false
      | Atom, List l1 -> false
      | List l, Var (varno, vt) -> unify t1 t0
      | Var (varno, vt), List l -> (
        match vt.instance with
        | Some inst -> unify inst t1
        | None ->
          vt.instance <- Some t1;
          trail#push t0;
          true
      )
      | Atom, Atom -> n0 = n1
      | Atom, Var (varno, vt) -> unify t1 t0
      | Var (varno, vt), Atom -> (
        match vt.instance with
        | Some inst -> unify inst t1
        | None ->
          vt.instance <- Some t1;
          trail#push t0;
          true
        )
      | Var (vn0, vt0), Var (vn1, vt1) -> (
        match vt0.instance, vt1.instance with
        | Some i0, None ->
          vt1.instance <- Some i0;
          trail#push t1;
          true
        | Some i0, Some i1 -> unify i0 i1
        | None, Some i1 ->
          vt0.instance <- Some i1;
          trail#push t0;
          true
        | None, None ->
          vt0.instance <- Some t1;
          trail#push t0;
          true
      )

  end

module Goal =
  struct

    type t = { name: IString.t; args: Term.t list; }

    let to_string (g: t) =
      let arg_strs = List.map (fun arg -> Term.string_of_term arg) g.args in
      let comma_separated_args = comma_separate arg_strs in
      Printf.sprintf "%s (%s)" (Interner.get_string g.name) comma_separated_args

    let rec unify_goals (self_args: Term.t list) (other_args: Term.t list) =
      match (self_args, other_args) with
      | [], [] -> true
      | [], h :: t -> false
      | h :: t, [] -> false
      | self_h :: self_t, other_h :: other_t ->
        if Term.unify self_h other_h then
          unify_goals self_t other_t
        else
          false

    let unify (other: t) (g: t) =
      if other.name = g.name then
        unify_goals g.args other.args
      else
        false

    let reset (g: t) = ignore (List.map (fun ter -> Term.reset ter ) g.args)
    let copy (g: t) = { name = g.name; args = (List.map (fun ter -> Term.copy ter ) g.args); }

  end

module Rule =
  struct

    type body = Goal of Goal.t * body | Nil
    type t = Goal.t * body

    let rec map_body f body =
      match body with
      | Nil -> []
      | Goal (g, b) -> (f g) :: map_body f b

    let string_of_body body = comma_separate (map_body Goal.to_string body)

    let rec string_of_rule ((goal, body): t) =
      let goal_string = Goal.to_string goal in
      let body_string = string_of_body body in
      Printf.sprintf "%s :- %s." goal_string body_string

    let rec append_to_body (lhs: body) (rhs: body) =
      match lhs with
      | Goal (goal, body) -> Goal(goal, append_to_body body rhs)
      | Nil -> rhs

  end

module Solver =
  struct


    module IStringMap = Map.Make(IString)

    type program = Rule.t list IStringMap.t

    type clause_state = Term.t option IStringMap.t

    type solver_state_t =
      {
        mutable program: program;
        mutable found_match: bool;
        mutable query: Goal.t;
      }

    let solver_state =
      {
        program = IStringMap.empty;
        found_match = false;
        query = { name = 0; args = []; };
      }

    let print_soln () = Printf.printf "%s\n" (Goal.to_string solver_state.query)

    let rec strip_clause_state (cl: Goal.t) =
      strip_clause_state_inner cl.args (IStringMap. empty)
    and strip_clause_state_inner (args: Term.t list) (state: clause_state) =
      match args with
      | [] -> state
      | (name, kind) :: tail ->
        match kind with
        | Var (varno, instance) ->
          let i = instance.instance in
          instance.instance <- None;
          strip_clause_state_inner tail IStringMap. (add varno i state)
        | _ -> strip_clause_state_inner tail state

    let rec resume_clause_state (cl: Goal.t) (state: clause_state) =
      resume_clause_state_inner cl.args state
    and resume_clause_state_inner (args: Term.t list) (state: clause_state) =
      match args with
      | [] -> state
      | (name, kind) :: tail ->
        match kind with
        | Var (varno, instance) ->
          instance.instance <- IStringMap.find varno state;
          resume_clause_state_inner tail state
        | _ -> resume_clause_state_inner tail state

    let rec try_unify_rule ((cl, rule_goals): Rule.t) (goals: Rule.body) =
      let t = Term.trail#mark in
      let clause_state = strip_clause_state cl in
      let res = match goals with
      | Nil -> false
      | Goal (g, goals_trail) ->
        if Goal.unify cl g then
          let unified_rules =
            match rule_goals with
            | Nil -> goals_trail
            | Goal (g, tail) -> Rule.append_to_body goals_trail rule_goals
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
      ignore (Term.trail#undo t);
      ignore (resume_clause_state cl clause_state);
      res

    and solve_inner (goals: Rule.body) =
      match goals with
      | Nil -> true
      | Goal (head, tail) ->
        match IStringMap. find_opt head.name solver_state.program with
        | None -> false
        | Some rules ->
          ignore (List.map (fun x -> try_unify_rule x goals) rules);
          true

    let solve (g: Goal.t) =
      solver_state.query <- g;
      solve_inner (Goal(g, Nil))

    let add_rule (name: IString.t) (rules: Rule.t list) = solver_state.program <- IStringMap. (add name rules solver_state.program)
  end


let var_x = Interner.intern "@x"
let var_y = Interner.intern "@y"
let var_z = Interner.intern "@z"
let my_list = Interner.intern "mylist"
let rule_name = Interner.intern "test"
let r: Rule.t =
  {
    name = rule_name;
    args = [Term.make_list_with_tail my_list [Term.make_var (Interner.intern "@boo") None; Term.make_atom ":cug"] { tail = None }]
  }, Nil
;;
let r2: Rule.t =
  {
    name = rule_name;
    args = [Term.make_list_with_tail my_list [Term.make_atom ":wew"; Term.make_atom ":jeffe"] { tail = None }]
  }, Nil
;;
Solver.add_rule rule_name [r; r2];;
let q: Goal.t =
  {
    name = rule_name;
    args = [Term.make_list_with_tail my_list [Term.make_var var_z None] { tail = None }];
  } ;;
Printf.printf "\nQuery: %s\nSolutions:\n" (Goal.to_string q);;
Solver.solve q

