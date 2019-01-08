open Lexer
open Lexing
open Printf
open Preast
open Core

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
;;

let in_channel_of_string s = In_channel.create s

let lex_buf_of_in_channel inch = Lexing.from_channel inch

let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a:  %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)
;;

match parse_with_error (lex_buf_of_in_channel (in_channel_of_string "tests/simple.pl")) with
| Some x -> printf "%s" (Preast.string_of_pre_ast x)
| None -> printf "sad"
