%token <string> ATOM
%token <string> RULE_NAME
%token <string> VAR_NAME
%token COMMA
%token RPAREN
%token LPAREN
%token IMPLIES
%token CUT
%token LBRACE
%token RBRACE
%token PIPE
%token EOR
%token EOF
%start <Preast.t option> prog
%%

prog:
  | v = rules { Some v }
;

rules: revrules = rev_rules; EOF { List.rev revrules };

rev_rules:
  | { [] }
  | tail = rev_rules; r = rule; EOR
    { r :: tail }
;

goal:
  | name = RULE_NAME; LPAREN; args = clause_args; RPAREN
    { name, args }
  | name = RULE_NAME
             { name, [] }
;

goal_list: rev_goals = rev_goal_list { List.rev rev_goals };

rev_goal_list:
  | { [] }
  | tail = rev_goal_list; COMMA; cl = goal
    { cl :: tail }
  | cl = goal
    { [cl] }
;

rule:
  | g = goal
    { g, [] }
  | g = goal; IMPLIES; goals = goal_list
    { g, goals }
;

clause_args: rev_args = rev_clause_args { List.rev rev_args };

rev_clause_args:
  | { [] }
  | tail = rev_clause_args; COMMA; cl = term
    { cl :: tail }
  | cl = term
    { [cl] }
;

term:
  | name = VAR_NAME
    { Preast. (Var' name) }
  | atom = ATOM
    { Preast. (Atom' atom) }
  | l = term_list
    { Preast. (List' l) }
;

rev_list_contents:
  | { [Preast. Nil'] }
  | tail = rev_list_contents; COMMA; it = term
    { (Preast. (Term' it)) :: tail }
  | tail = rev_list_contents; PIPE; var = VAR_NAME
    { (Preast. (Tail' var)) :: tail }
  | it = term { [Preast. (Term' it)] }
;
term_list: LBRACE; items = rev_list_contents; RBRACE { List.rev items };
