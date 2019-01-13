{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let newline = '\r' | '\n' | "\r\n"
let whitespace = [' ' '\t' ]+
let id = ['a' - 'z' 'A'-'Z' '_'] ['a' - 'z' 'A'-'Z' '_' '0'-'9']*
let atom = ':' ['a' - 'z' 'A'-'Z' '_' '0'-'9']*
let var = '@' ['a' - 'z' 'A'-'Z' '_' '0'-'9']*

rule read =
  parse
  | whitespace { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | id { RULE_NAME (Lexing.lexeme lexbuf) }
  | var { VAR_NAME (Lexing.lexeme lexbuf) }
  | atom { ATOM (Lexing.lexeme lexbuf) }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LBRACE }
  | ']' { RBRACE }
  | ":-" { IMPLIES }
  | '.' { EOR }
  | ',' { COMMA }
  | eof { EOF }
  | '|' { PIPE }
  | '!' { CUT }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
