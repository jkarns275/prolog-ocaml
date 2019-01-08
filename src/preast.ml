open Interner

type term =
  | Atom' of string
  | Var' of string
;;

type goal = string * term list

type rule = goal * goal list

type t = rule list

let string_of_term t =
  match t with
  | Atom' s -> s
  | Var' s -> s
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
