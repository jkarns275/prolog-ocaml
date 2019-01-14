open Interner
open Hashtbl
open Preast
open Batteries

let rec comma_separate strings =
  match strings with
  | [] -> ""
  | head :: [] -> head
  | head :: tail -> Printf.sprintf "%s, %s" head (comma_separate tail)

module Term =
  struct

    type _varno_counter_t = { mutable n: int; }
    let _varno_counter = { n = 0; }
    type var_t = { mutable instance: t option; name: IString.t; varno: int; }
    and term_list =
      | TList of t * term_list
      | Tail of var_t
      | Nil
    and t =
      | Var of var_t
      | List of term_list
      | Atom of IString.t

    let rec map_term_list f tl =
      match tl with
      | TList (term, tail) -> (f term) :: map_term_list f tail
      | Nil -> []
      | Tail t ->
        match t.instance with
        | Some t -> [f t]
        | None -> []

    let make_atom (is: string) = Atom (Interner.intern is)
    let next_varno () =
      let varno = _varno_counter.n in
      _varno_counter.n <- varno + 1;
     varno
    let rec make_list (terms: t list) =
      match terms with
      | [] -> Nil
      | term :: tail -> TList (term, make_list tail)
    let rec make_list_with_tail_inner (terms: t list) (tail: var_t) =
      match terms with
      | [] -> Tail tail
      | term :: t -> TList (term, make_list_with_tail_inner t tail)
    and make_list_with_tail (name: IString.t) (terms: t list) (tail: var_t) =
      name, List (make_list_with_tail_inner terms tail)

    let rec make_var_internal name instance =
      let varno = next_varno () in
      { instance; varno; name;  }
    and make_var name instance =
      let vt = make_var_internal name instance in
      Var vt

    let rec copy_term_list tl =
      match tl with
      | TList (term, tail) -> TList (copy term, copy_term_list tail)
      | Nil -> Nil
      | Tail tt -> (
        let vt = copy_var tt in
        Tail vt
      )
    and copy_var (vt: var_t): var_t =
      let inst = BatOption.map copy vt.instance in
      make_var_internal vt.name inst
    and copy (term: t) =
      match term with
      | Var vt -> Var (copy_var vt)
      | Atom name -> term
      | List l -> List (copy_term_list l)

    let rec reset (term: t) =
      match term with
      | Var vt ->
        vt.instance <- None;
        ()
      | List l -> ignore (map_term_list (fun term -> reset term) l)
      | Atom _ -> ()
    exception ThisShouldNotHappen of string
    let rec string_of_term_list (tl: term_list) = Printf.sprintf "[%s]" (string_of_term_list_inner tl)
    and string_of_term_list_inner (tl: term_list) =
      match tl with
      | TList (term, tail) -> Printf.sprintf "%s, %s" (string_of_term term) (string_of_term_list_inner tail)
      | Nil -> ""
      | Tail tail -> (
        match tail.instance with
        | Some(Var vt) -> (
          match vt.instance with
          | None -> Printf.sprintf "| %s" (string_of_term (Var vt))
          | Some t -> Printf.sprintf "%s " (string_of_term_list_inner (Tail vt))
        )
        | Some(Atom name) -> raise (ThisShouldNotHappen "Damn")
        | Some(List l) -> Printf.sprintf "%s" (string_of_term_list_inner l)
        | None -> Printf.sprintf "| %s" (string_of_term (Var tail))
      )

    and string_of_term (term: t) =
      match term with
      | List l -> string_of_term_list l
      | Atom name -> Interner.get_string name
      | Var vt ->
        match vt.instance with
        | Some x -> string_of_term x
        | None -> Printf.sprintf "%d%s" vt.varno (Interner.get_string vt.name)

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
        match t.instance with
        | Some tail -> false
        | None -> true
      )
      | TList (t0, tail), Tail t1 -> unify_lists l1 l0
      | Tail t0, TList (t1, tail) -> (
        match t0.instance with
        | Some t -> unify t (List tail)
        | None ->
          t0.instance <- Some (List l1);
          trail#push (List l0);
          true
      )
      | Tail t0, Tail t1 -> (
        match t0.instance, t1.instance with
        | Some tail0, Some tail1 -> unify tail0 tail1
        | Some tail0, None ->
          t1.instance <- Some tail0;
          trail#push (List l1);
          true
        | None, Some tail1 ->
          t0.instance <- Some tail1;
          trail#push (List l0);
          true
        | None, None ->
          t0.instance <- Some (List l1);
          trail#push (List l0);
          true
      )
      | TList _, Nil -> false
      | Nil, TList _ -> false
      | Nil, Nil -> true

    and unify (t0: t) (t1: t) =
      match t0, t1 with
      | List l0, List l1 -> unify_lists l0 l1
      | List _, Atom _ -> false
      | Atom _, List _ -> false
      | List l, Var vt -> unify t1 t0
      | Var vt, List l -> (
        match vt.instance with
        | Some inst -> unify inst t1
        | None ->
          vt.instance <- Some t1;
          trail#push t0;
          true
      )
      | Atom n0, Atom n1 -> n0 = n1
      | Atom n0, Var vt -> unify t1 t0
      | Var vt, Atom name -> (
        match vt.instance with
        | Some inst -> unify inst t1
        | None ->
          vt.instance <- Some t1;
          trail#push t0;
          true
        )
      | Var vt0, Var vt1 -> (
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
  type var_cache_t = { mutable s2v: Term.var_t IStringMap.t; }
  let var_cache = { s2v = IStringMap.empty }

  type t = Rule.t list IStringMap.t

  let get_var name =
    try IStringMap.find name var_cache.s2v
    with Not_found ->
      let vt = Term.make_var_internal name None in
      var_cache.s2v <- IStringMap.add name vt var_cache.s2v;
      vt
  let intern s = Interner.intern s
  let rec term_list_from_preast (t: Preast.list_term list): Term.term_list =
    match t with
    | [] -> Nil
    | (Tail' s) :: t -> Tail (Term.make_var_internal (intern s) None)
    | (Term' h) :: t -> TList (term_from_preast h, term_list_from_preast t)
    | Nil' :: t -> Nil
  and term_from_preast (t: Preast.term): Term.t =
    match t with
    | Atom' str -> Atom (intern str)
    | Var' str -> Term.make_var (intern str) None
    | List' l ->
      let terms = term_list_from_preast l in
      List terms

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
    List.fold_left (fun acc k -> IStringMap.add k (Hashtbl.find_all tbl k) acc) IStringMap.empty
      (List.map (fun (k, v) -> k) (Hashtbl.to_list tbl))

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
      | term :: tail ->
        match term with
        | Var vt ->
          let i = vt.instance in
          vt.instance <- None;
          strip_clause_state_inner tail IStringMap. (add vt.varno i state)
        | _ -> strip_clause_state_inner tail state

    let rec resume_clause_state ((name, args): Goal.t) (state: clause_state) =
      resume_clause_state_inner args state
    and resume_clause_state_inner (args: Term.t list) (state: clause_state) =
      match args with
      | [] -> state
      | term :: tail ->
        match term with
        | Var vt ->
          vt.instance <- IStringMap.find vt.varno state;
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
        try (
          let rules = IStringMap.find name solver_state.program in
          ignore (List.map (fun x -> try_unify_rule x goals) rules);
          true
        )
        with Not_found -> false

    let solve (g: Goal.t) =
      solver_state.query <- g;
      solve_inner [g]

    let add_rule (name: IString.t) (rules: Rule.t list) = solver_state.program <- IStringMap. (add name rules solver_state.program)
  end

open Lexer
open Lexing
open Preast
let c = List.map (fun x -> Printf.printf "%d\n" x) [1;2;3;4];;

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
;;

let lex_buf_of_in_channel inch = Lexing.from_channel inch

let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
    Printf.fprintf stderr "%a:  %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)
;;

exception ParseException of string

let p =
  match parse_with_error (lex_buf_of_in_channel BatFile. (open_in "tests/simple.pl")) with
  | Some x -> Ast.from_preast x
  | None -> raise (ParseException "Failed to parse.")
;;

open BatEnum
let print_rules (rules: Rule.t list) = ignore (List.map (fun v -> Printf.printf "%s\n" (Rule.string_of_rule v)) rules);;
let keys = BatEnum.iter print_rules (IStringMap.values p);;

Solver.solver_state.program <- p

let q: Goal.t =
  (
    Interner.intern "zzyzz",
    [List (TList (Term.make_var (Interner.intern "@z") None, TList (Term.make_var (Interner.intern "@x") None, Tail (Term.make_var_internal (Interner.intern "@T") None))))]
  ) ;;
Printf.printf "\nQuery: %s\nSolutions:\n" (Goal.to_string q);;
Solver.solve q


