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
let hex_integer = ("0x" | "0X") ['a'-'F''A'-'F''0'-'9' '_']
let oct_integer = ("0O" | "0o") ['0'-'7' '_']+
let bin_intger = ("0B" | "0b") ['0' '1' '_']+
let dec_digit = ['0'-'9' '_']
let dec_integer = dec_digit+
let int = ('-' | '+')? hex_integer | dec_integer
let frac = dec_digit*
let exp = ['e' 'E'] ['-' '+']? dec_digit+
let float = dec_digit+ '.' frac exp?


rule read =
  parse
  | whitespace { read lexbuf }
  | newline { next_line lexbuf; read lexbuf }
  | id { RULE_NAME (Lexing.lexeme lexbuf) }
  | var { VAR_NAME (Lexing.lexeme lexbuf) }
  | atom { ATOM (Lexing.lexeme lexbuf) }
  | int { FLOAT (float_of_int (int_of_string (Lexing.lexeme lexbuf))) }
  | float { FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
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
  | '+' { ADD }
  | '-' { SUB }
  | '/' { DIV }
  | '*' { MUL }
  | '%' { MOD }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
