open OUnit
open Lppterm

(* Parsing functions *)

let parse_term str =
  Parser.term Lexer.token (Lexing.from_string str)

let parse_lppterm str =
  Top_parser.lppterm Top_lexer.token (Lexing.from_string str)

let parse_clauses str =
  Parser.clauses Lexer.token (Lexing.from_string str)

let read_mod filename =
  Parser.clauses Lexer.token (Lexing.from_channel (open_in filename))

let eval_clauses = read_mod "eval.mod"
let pcf_clauses = read_mod "pcf.mod"
let fsub_clauses = read_mod "fsub.mod"
let add_clauses = read_mod "add.mod"
  
(* Custom asserts *)
    
let id x = x

let assert_pprint_equal s t =
  assert_equal ~printer:id s (lppterm_to_string t)

let assert_int_equal = assert_equal ~printer:string_of_int
