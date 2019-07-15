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

    type ari_op = Add | Sub | Mul | Div | Mod

    type var_t = { mutable instance: t option; name: IString.t; varno: int; }
    and num_t = { mutable trace: float list; mutable value: float; }
    and expr_t = t * ari_op * t
    and term_list =
      | TList of t * term_list
      | Tail of var_t
      | Nil
    and t =
      | Var of var_t
      | List of term_list
      | Atom of IString.t
      | Number of num_t
      | Expr of expr_t

    let rec tailed tl =
      match tl with
      | TList (term, tail) -> tailed tail
      | Nil -> false
      | Tail _ -> true

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

    let make_number n = { trace = [n]; value = n; }

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
      | Number n -> Number { trace = n.trace; value = n.value; }
      | Expr (lhs, op, rhs) -> Expr (copy lhs, op, copy rhs)

    let rec eval_term term =
      match term with
      | Number n -> Some n.value
      | Expr e -> eval_expr e
      | Var v -> (
        match v.instance with
        | None -> None
        | Some t -> eval_term t
      )
      | _ -> None

    and eval_expr ((lhs, op, rhs): expr_t) =
      match eval_term lhs, eval_term rhs with
      | Some n0, Some n1 -> Some (
        match op with
        | Add -> n0 +. n1
        | Sub -> n0 -. n1
        | Mul -> n0 *. n1
        | Div -> n0 /. n1
        | Mod -> mod_float n0 n1
      )
      | _ -> None

    exception ThisShouldNotHappen of string

    let rec reset (term: t) =
      match term with
      | Var vt ->
        vt.instance <- None;
        ()
      | List l -> ignore (map_term_list (fun term -> reset term) l)
      | Number n -> (
        match n.trace with
        | [] -> raise (ThisShouldNotHappen "This should not happen")
        | _ :: [] -> raise (ThisShouldNotHappen "This should not happen")
        | _ :: tail -> n.trace <- tail
      )
      | Atom _ -> ()
      | Expr _ -> ()

  let string_of_ari_op a =
    match a with
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | Mod -> "%"

  let rec string_of_term_list (tl: term_list) = Printf.sprintf "[%s]" (string_of_term_list_inner tl)
    and string_of_term_list_inner (tl: term_list) =
      match tl with
      | TList (term, tail) -> Printf.sprintf "%s, %s" (string_of_term term) (string_of_term_list_inner tail)
      | Nil -> "<nil>"
      | Tail tail -> (
        match tail.instance with
        | Some(Var vt) -> (
          match vt.instance with
          | None -> Printf.sprintf "| %s" (string_of_term (Var vt))
          | Some t -> Printf.sprintf " %s " (string_of_term_list_inner (Tail vt))
        )
        | Some(Atom name) -> raise (ThisShouldNotHappen "This should not happen")
        | Some(List l) -> Printf.sprintf "%s" (string_of_term_list_inner l)
        | Some(e) -> Printf.sprintf "%s" (string_of_term e)
        | None -> Printf.sprintf "%s" (string_of_term (Var tail))
      )

    and string_of_term (term: t) =
      match term with
      | List l -> string_of_term_list l
      | Atom name -> Printf.sprintf "%s" (Interner.get_string name)
      | Number n -> Printf.sprintf "%f" n.value
      | Expr (lhs, op, rhs) -> (
        match eval_expr (lhs, op, rhs) with
        | None -> Printf.sprintf "%s %s %s" (string_of_term lhs) (string_of_ari_op op) (string_of_term rhs)
        | Some n -> Printf.sprintf "%f" n
      )
      | Var vt -> (
        match vt.instance with
        | Some x -> Printf.sprintf "%s" (string_of_term x)
        | None -> Printf.sprintf "%d%s" vt.varno (Interner.get_string vt.name)
      )

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

    (* Fix issue where [x, ] unfies with [] *)
    (* Turns out: order matters for unification.
       Example:
        If the question has an empty tail as an argument which corresponds to a list on the other end that has two elements.
        Right now the program will append the list to the end of the tail, but thats not what we want: since the tailand the argument .
     *)
    let rec unify_lists (l0: term_list) (l1: term_list) =
      match l0, l1 with
      | TList (t0, tail0), TList (t1, tail1) ->
        if unify t0 t1 then unify_lists tail0 tail1 else false
      | Nil, Tail t -> unify_lists l1 l0
      | Tail t, Nil -> (
        match t.instance with
        | Some _ -> false
        | None ->
          t.instance <- Some (List l1);
          trail#push (List l0);
          true
      )
      | TList (t0, tail), Tail t1 -> unify_lists l1 l0
      | Tail t0, TList (t1, tail) -> (
        match t0.instance with
        | Some t -> unify t (List l1)
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
      | Expr n, Var vt -> (
        match vt.instance with
        | Some it -> unify t0 it
        | None -> vt.instance <- Some t0; trail#push t1; true
      )
      | Expr e, Number n1 -> (
        match eval_expr e with
        | Some n0 -> n0 == n1.value
        | None -> false
      )
      | Number _, Expr _ -> unify t1 t0
      | Var _, Expr _ -> unify t1 t0
      | Number n0, Number n1 -> n0.value == n1.value
      | Number n, Var vt -> (
        match vt.instance with
        | Some it -> unify t0 it
        | None -> vt.instance <- Some t0; trail#push t1; true
      )
      | Var vt, Number n -> unify t1 t0
      | Number _, _ -> false
      | _, Number _ -> false
      | _, Expr _ -> false
      | Expr _, _ -> false
  end

module Goal =
  struct

    type cmp_op = Eq | Neq | Gt | Gte | Lt | Lte
    type cmp_t = { lhs: Term.t; op: cmp_op; rhs: Term.t }

    let string_of_cmp_op c =
      match c with
      | Eq -> "="
      | Neq -> "!="
      | Gt -> ">"
      | Gte -> ">="
      | Lt -> "<"
      | Lte -> "<="

    let string_of_cmp (c: cmp_t) =
      Printf.sprintf "%s %s %s" (Term.string_of_term c.lhs) (string_of_cmp_op c.op) (Term.string_of_term c.rhs)

    type clause_t = { name: IString.t; args: Term.t list; }
    type t =
      | Clause of clause_t
      | Cmp of cmp_t

    let string_of_clause (cl: clause_t) =
      let arg_strs = List.map (fun arg -> Term.string_of_term arg) cl.args in
      let comma_separated_args = comma_separate arg_strs in
      Printf.sprintf "%s (%s)" (Interner.get_string cl.name) comma_separated_args

    let to_string (goal: t) =
      match goal with
      | Cmp c -> string_of_cmp c
      | Clause cl -> string_of_clause cl

    let rec unify_goal_args (other_args: Term.t list) (self_args: Term.t list) =
      match (self_args, other_args) with
      | [], [] -> true
      | [], h :: t -> false
      | h :: t, [] -> false
      | other_h :: other_t, self_h :: self_t ->
        if Term.unify self_h other_h then
          unify_goal_args self_t other_t
        else
          false

    let unify (other: clause_t) (self: clause_t) =
      if other.name = self.name then
        unify_goal_args self.args other.args
      else
        false

    let reset (cl: clause_t) = ignore (List.map (fun ter -> Term.reset ter ) cl.args)
    let copy_clause (cl: clause_t) = { name = cl.name; args = List.map (fun ter -> Term.copy ter ) cl.args; }
    let copy (g: t) =
      match g with
      | Cmp c -> Cmp { lhs = Term.copy c.lhs; rhs = Term.copy c.rhs; op = c.op }
      | Clause c -> Clause (copy_clause c)
  end

module Rule =
  struct

    type body = Goal.t list
    type t = Goal.clause_t * body

    let string_of_body body = comma_separate (List.map Goal.to_string body)

    let rec string_of_rule ((clause, body): t) =
      let goal_string = Goal.string_of_clause clause in
      match body with
      | [] -> Printf.sprintf "%s." goal_string
      | _ ->
        let body_string = string_of_body body in
        Printf.sprintf "%s :- %s." goal_string body_string

    let rec append_to_body (lhs: body) (rhs: body) =
      match lhs with
      | goal :: tail -> goal :: append_to_body tail rhs
      | [] -> rhs

    (*let copy ((cl, body): t) = (Goal.copy_clause cl, List.map Goal.copy body)*)

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
    | (Tail' s) :: t -> Tail (intern s |> get_var)
    | (Term' h) :: t -> TList (term_from_preast h, term_list_from_preast t)
    | Nil' :: t -> Nil
  and expr_from_mult (e: Preast.expr) (tail: (mul_op * expr) list) =
    match tail with
    | [] -> expr_from_preast_expr e
    | (o, expr) :: tail ->
      let op =
        match o with
        | Mul -> Term. Mul
        | Div -> Term. Div
        | Mod -> Term. Mod
      in
      Term. Expr ((expr_from_preast_expr e), op, (expr_from_mult expr tail))
  and expr_from_addit (e: Preast.expr) (tail: (add_op * expr) list) =
    match tail with
    | [] -> expr_from_preast_expr e
    | (o, expr) :: tail ->
      let op = (
        match o with
        | Sub -> Term. Sub
        | Add -> Term. Add
      ) in
      Term. Expr ((expr_from_preast_expr e), op, (expr_from_addit expr tail))
  and expr_from_preast_expr (e: Preast.expr): Term.t =
    match e with
    | Number' n -> Term. Number (Term.make_number n)
    | Addit' (e, tail) -> expr_from_addit e tail
    | Mult' (e, tail) -> expr_from_mult e tail
    | EVar' name -> Term. Var (get_var (intern name))
  and term_from_preast (t: Preast.term): Term.t =
    match t with
    | Atom' str -> Atom (intern str)
    | Var' str -> Term. Var (get_var (intern str))
    | List' l ->
      let terms = term_list_from_preast l in
      List terms
    | Expr' e -> expr_from_preast_expr e

  let clause_from_preast ((name, args): Preast.goal) = Goal. { name = Interner.intern name; args = List.map term_from_preast args }

  let rule_from_preast ((cl, goals): Preast.rule) =
    var_cache.s2v <- IStringMap.empty;
    let clause = clause_from_preast cl in
    let goals = List.map (fun x -> Goal. (Clause (clause_from_preast x))) goals in
    clause, goals

  let from_preast (p: Preast.t) =
    let tbl = Hashtbl.create (List.length p) in
    let add_rule (r: Rule.t) =
      let cl, goals = r in
      Hashtbl.add tbl cl.name r
    in
    ignore (List.map add_rule (List.map rule_from_preast p));
    List.fold_left (fun acc k -> IStringMap.add k (Hashtbl.find_all tbl k) acc) IStringMap.empty
      (List.map (fun (k, v) -> k) (Hashtbl.to_list tbl))

  end

module Solver =
  struct

    type program = Preast.rule list IStringMap.t

    type clause_state = Term.t option IStringMap.t

    type solver_state_t =
      {
        mutable program: program;
        mutable found_match: bool;
        mutable queries: Goal.t list;
      }

    let solver_state =
      {
        program = IStringMap.empty;
        found_match = false;
        queries = [Goal. (Clause { name = 0; args = []; })];
      }

    let print_soln () =
      let str = (List.fold_left (fun acc g -> Printf.sprintf "%s    %s,\n" acc (Goal.to_string g)) "" solver_state.queries) in
      Printf.printf "SOLUTION:\n%s" str

    let rec strip_clause_state (cl: Goal.clause_t) =
      strip_clause_state_inner cl.args (IStringMap. empty)
    and strip_list_state (l: Term.term_list) (state: clause_state) =
      match l with
      | Nil -> state
      | Tail vt -> (
        let i = vt.instance in
        vt.instance <- None;
        IStringMap.add vt.varno i state
      )
      | TList (t, tail) -> (
        let new_state = strip_term_state t state in
        strip_list_state tail new_state
      )
    and strip_expr_state ((lhs, _op, rhs): Term.expr_t) (state: clause_state) =
      strip_term_state lhs state |> strip_term_state rhs
    and strip_term_state (term: Term.t) (state: clause_state) =
      match term with
        | Var vt -> (
          let i = vt.instance in
          vt.instance <- None;
          IStringMap.add vt.varno i state
        )
        | List l -> strip_list_state l state
        | Expr e -> strip_expr_state e state
        | _ -> state
    and strip_clause_state_inner (args: Term.t list) (state: clause_state) =
      match args with
      | [] -> state
      | term :: tail ->
        let new_state = strip_term_state term state in
        strip_clause_state_inner tail new_state

    let rec resume_clause_state (cl: Goal.clause_t) (state: clause_state) =
      resume_clause_state_inner cl.args state
    and resume_clause_state_inner (args: Term.t list) (state: clause_state) =
      match args with
      | [] -> state
      | term :: tail ->
        match term with
        | Var vt ->
          vt.instance <- IStringMap.find vt.varno state;
          resume_clause_state_inner tail state
        | _ -> resume_clause_state_inner tail state

    let rec try_unify_rule ((cl, rule_goals): Rule.t) (qgoals: Rule.body) =
      let t = Term.trail#mark in
      (*let clause_state = strip_clause_state cl in*)
      let res = match qgoals with
      | [] -> false
      | g :: goals_trail -> (
        match g with
        | Clause qcl -> (
          if Goal.unify cl qcl then
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
        )
        | _ -> raise (Term.ThisShouldNotHappen "")
      )
      in
      ignore (Term.trail#undo t);
      (*ignore (resume_clause_state cl clause_state);*)
      res

    and solve_inner (goals: Rule.body) =
      match goals with
      | [] -> true
      | Cmp c :: tail -> (
        match Term.eval_term c.lhs with
        | Some n0 -> (
          match Term.eval_term c.rhs with
          | Some n1 -> (
            match c.op with
            | Lt -> n0 < n1
            | Lte -> n0 <= n1
            | _ -> false
          )
          | None -> false
        )
        | None -> false)
      | Clause cl :: tail ->
        try (
          let rules = IStringMap.find cl.name solver_state.program in
          ignore (List.map (fun x -> try_unify_rule x goals) (List.map Ast.rule_from_preast rules));
          true
        )
        with Not_found -> false

    let solve (g: Goal.t) =
      solver_state.queries <- [g];
      solve_inner [g]

    let solve_all (g: Goal.t list) =
      solver_state.queries <- g;
      solve_inner g

    let add_rule (name: IString.t) (rules: Preast.rule list) = solver_state.program <- IStringMap. (add name rules solver_state.program)
  end

open Lexer
open Lexing
open Preast

module Cli =
  struct


    let position_to_string filename lexbuf =
      let pos = lexbuf.lex_curr_p in
      Printf.sprintf "%s:%d:%d" filename pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

    let make_query_parse_error filename lexbuf =
      let pos = lexbuf.lex_curr_p in
      Printf.sprintf "\"%s\" %d:%d" filename pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

    let lex_buf_of_in_channel inch = Lexing.from_channel inch
    let lex_buf_of_string s = Lexing.from_string s

    let parse_file_with_error filename lexbuf =
      try Some (Parser.prog Lexer.read lexbuf) with
      | SyntaxError msg ->
        Printf.fprintf stderr "%s:  %s\n" (position_to_string filename lexbuf) msg;
        None
      | Parser.Error ->
        Printf.fprintf stderr "%s: syntax error\n" (position_to_string filename lexbuf);
        exit (-1)

    let parse_query_with_error query_str lexbuf =
      try Some (Parser.query Lexer.read lexbuf) with
      | SyntaxError msg ->
        Printf.printf "%s:  %s\n" (make_query_parse_error query_str lexbuf) msg;
        None
      | Parser.Error ->
        Printf.printf "%s: syntax error\n" (make_query_parse_error query_str lexbuf);
        None

    let test  lb =
      try ignore (Parser.query Lexer.read lb) with
      | SyntaxError msg -> ()
      | _ -> ()

    exception ParseException of string

    type pre_program = (IString.t, Preast.rule) Hashtbl.t

    let make_empty_pre_program (): pre_program = Hashtbl.create 16
    let add_to_pre_program (parsed: Preast.t) (p: pre_program): pre_program =
      let add_rule (r: Preast.rule) =
        let (name, _args), _goals = r in
        Hashtbl.add p (Interner.intern name) r
      in
      ignore (List.map add_rule parsed);
      p

    let program_of_pre_program (p: pre_program): Solver.program =
      let keys = List.map (fun (k, v) -> k) (Hashtbl.to_list p) in
      List.fold_left (fun acc k -> IStringMap.add k (Hashtbl.find_all p k) acc) IStringMap.empty keys

    let parse_file path =
      match parse_file_with_error path (lex_buf_of_in_channel BatFile. (open_in path)) with
      | Some x -> x
      | None -> raise (ParseException "Failed to parse.")

    (* ignore the first argument, because it is the program's file not the first user supplied argument *)
    let rec read_input_files () =
       match Array.to_list Sys.argv with
       | _head :: input_files -> read_input_files_inner input_files
       | [] -> program_of_pre_program (make_empty_pre_program ())
    and read_input_files_inner (input_files: string list) =
      let prog = make_empty_pre_program () in
      ignore (List.map (fun file -> add_to_pre_program (parse_file file) prog) input_files);
      program_of_pre_program prog

    exception Break of int

    let handle_query (qs: string) =
      try (
        let s = (qs ^ " .") in
        match parse_query_with_error qs (lex_buf_of_string s) with
        | Some x ->
          ignore (Solver.solve_all (List.map (fun y -> Goal.Clause (Ast.clause_from_preast y)) x))
        | None -> ()
      ) with _ -> ()

    let interactive (program: Solver.program) =
      Solver.solver_state.program <- program;
      try
        while true do
          Printf.printf ":? ";
          let line = read_line() in
          match line with
          | "exit" -> raise (Break 0)
          | "quit" -> raise (Break 0)
          | s -> handle_query s
        done
      with
        | End_of_file -> ()
        | Break _ -> ()

    let run () =
      match Array.length Sys.argv with
      | 0 -> () (* Not possible? *)
      | 1 -> Printf.printf "Please supply at least one input file.\n" (* No input supplied *)
      | x -> interactive (read_input_files ())

  end
;;

Cli.run ()

(*
open BatEnum
let print_rules (rules: Rule.t list) = ignore (List.map (fun v -> Printf.printf "%s\n" (Rule.string_of_rule v)) rules);;
Printf.printf "RULES:\n";;
let keys = BatEnum.iter print_rules (IStringMap.values (Ast.from_preast p));;
let create_program (p: Preast.t) =
  let tbl = Hashtbl.create (List.length p) in
  let add_rule (r: Preast.rule) =
    let (name, args), goals = r in
    Hashtbl.add tbl (Interner.intern name) r
  in
  ignore (List.map add_rule p);
  List.fold_left (fun acc k -> IStringMap.add k (Hashtbl.find_all tbl k) acc) IStringMap.empty
    (List.map (fun (k, v) -> k) (Hashtbl.to_list tbl))
;;

Solver.solver_state.program <- create_program p;;

Printf.printf "\n\n";;

let q: Goal.clause_t =
  Goal. {
    name = Interner.intern "len";
    args = [List (TList (Term.make_atom "A", TList (Term. make_atom "x", Nil))); Term. make_var (Interner.intern "hy") None];

  } ;;
Printf.printf "\nQuery: %s\n" (Goal.string_of_clause q);;
Solver.solve (Clause q)
*)

