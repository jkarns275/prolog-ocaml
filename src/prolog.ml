open Interner
open Hashtbl
open Preast

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
    and tail_t = { mutable tail: term_list option; name: IString.t; }
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

    let make_tail (name: IString.t) (tail: term_list option) = { name; tail; }

    let rec copy_term_list tl =
      match tl with
      | TList (term, tail) -> TList (copy term, copy_term_list tail)
      | Nil -> Nil
      | Tail tt -> Tail (make_tail tt.name tt.tail)
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
          | None -> Printf.sprintf "%s | %s" (string_of_term term) (Interner.get_string t.name)
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

    type t = IString.t * Term.t list

    let to_string ((name, args): t) =
      let arg_strs = List.map (fun arg -> Term.string_of_term arg) args in
      let comma_separated_args = comma_separate arg_strs in
      Printf.sprintf "%s (%s)" (Interner.get_string name) comma_separated_args

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

    let unify ((other_name, other_args): t) ((name, args): t) =
      if other_name = name then
        unify_goals args other_args
      else
        false

    let reset ((_, args): t) = ignore (List.map (fun ter -> Term.reset ter ) args)
    let copy ((name, args): t) = name, List.map (fun ter -> Term.copy ter ) args

  end

module Rule =
  struct

    type body = Goal.t list
    type t = Goal.t * body

    let string_of_body body = comma_separate (List.map Goal.to_string body)

    let rec string_of_rule ((goal, body): t) =
      let goal_string = Goal.to_string goal in
      let body_string = string_of_body body in
      Printf.sprintf "%s :- %s." goal_string body_string

    let rec append_to_body (lhs: body) (rhs: body) =
      match lhs with
      | goal :: tail -> goal :: append_to_body tail rhs
      | [] -> rhs

  end

module IStringMap = Map.Make (IString)

module Ast =
  struct

  type var_cache_t = { mutable s2v: Term.t IStringMap.t; }
  let var_cache = { s2v = IStringMap.empty }

  type t = Rule.t list IStringMap.t

  let term_from_preast (t: Preast.term): Term.t =
    match t with
    | Atom' str -> Interner.intern str, Atom
    | Var' str ->
      let name = Interner.intern str in
      match IStringMap.find_opt name var_cache.s2v with
      | Some v -> v
      | None ->
        let var = Term.make_var name None in
        var_cache.s2v <- IStringMap.add name var var_cache.s2v;
        var


  let goal_from_preast ((name, args): Preast.goal) = Interner.intern name, List.map term_from_preast args

  let rule_from_preast ((cl, goals): Preast.rule) =
    var_cache.s2v <- IStringMap.empty;
    let clause = goal_from_preast cl in
    let goals = List.map goal_from_preast goals in
    clause, goals

  let from_preast (p: Preast.t) =
    let tbl = Hashtbl.create (List.length p) in
    let add_rule (r: Rule.t) =
      let (name, args), goals = r in
      Hashtbl.add tbl name r
    in
    ignore (List.map add_rule (List.map rule_from_preast p));
    Seq.fold_left (fun acc k -> IStringMap.add k (Hashtbl.find_all tbl k) acc) IStringMap.empty (Hashtbl.to_seq_keys tbl)

  end

module Solver =
  struct

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
        query = 0, [];
      }

    let print_soln () = Printf.printf "%s\n" (Goal.to_string solver_state.query)

    let rec strip_clause_state ((name, args): Goal.t) =
      strip_clause_state_inner args (IStringMap. empty)
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

    let rec resume_clause_state ((name, args): Goal.t) (state: clause_state) =
      resume_clause_state_inner args state
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
      | [] -> false
      | g :: goals_trail ->
        if Goal.unify cl g then
          let unified_rules =
            match rule_goals with
            | [] -> goals_trail
            | g :: tail -> Rule.append_to_body goals_trail rule_goals
          in
          match unified_rules with
          | [] ->
            solver_state.found_match <- true;
            print_soln ();
            true
          | g :: tail -> solve_inner unified_rules
        else
          false
      in
      ignore (Term.trail#undo t);
      ignore (resume_clause_state cl clause_state);
      res

    and solve_inner (goals: Rule.body) =
      match goals with
      | [] -> true
      | (name, args) :: tail ->
        match IStringMap. find_opt name solver_state.program with
        | None -> false
        | Some rules ->
          ignore (List.map (fun x -> try_unify_rule x goals) rules);
          true

    let solve (g: Goal.t) =
      solver_state.query <- g;
      solve_inner [g]

    let add_rule (name: IString.t) (rules: Rule.t list) = solver_state.program <- IStringMap. (add name rules solver_state.program)
  end



let q: Goal.t =
  (
    Interner.intern "zzyzz",
    [0, List (Term.make_list [Term.make_var (Interner.intern "z") None; Term.make_var (Interner.intern "x") None])]
  ) ;;
Printf.printf "\nQuery: %s\nSolutions:\n" (Goal.to_string q);;
Solver.solve q

