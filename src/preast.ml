open Interner

type mul_op = Mul | Div | Mod
type add_op = Add | Sub

type expr =
  | Number' of float
  | EVar' of string
  | Addit' of expr * (add_op * expr) list
  | Mult' of expr * (mul_op * expr) list
;;

type term =
  | Expr' of expr
  | Atom' of string
  | Var' of string
  | List' of list_term list
and list_term =
  | Nil'
  | Term' of term
  | Tail' of string
;;

type goal = string * term list

type rule = goal * goal list

type t = rule list

let string_of_term t =
  match t with
  | Atom' s -> s
  | Var' s -> s
  | List' s -> "fill me in later"
  | Expr' _ -> "expr..."
;;

let rec string_of_term_list ts =
  match ts with
  | [] -> ""
  | h :: [] -> Printf.sprintf "%s" (string_of_term h)
  | h :: t -> Printf.sprintf "%s, %s" (string_of_term h) (string_of_term_list t)
;;

let string_of_goal ((name, args): goal) =
  match args with
  | [] -> name
  | _ -> Printf.sprintf "%s (%s)" name (string_of_term_list args)
;;

let rec string_of_goal_list gs =
  match gs with
  | [] -> ""
  | h :: [] -> Printf.sprintf "%s" (string_of_goal h)
  | h :: t -> Printf.sprintf "%s, %s" (string_of_goal h) (string_of_goal_list t)
;;

let string_of_rule ((g, goals): rule) =
  let goal_str = string_of_goal g in
  match goals with
  | [] -> goal_str
  | goals -> Printf.sprintf "%s :- %s" goal_str (string_of_goal_list goals)
;;

let rec string_of_pre_ast a =
  match a with
  | [] -> ""
  | h :: tail -> Printf.sprintf "%s.\n%s" (string_of_rule h) (string_of_pre_ast tail)
;;
