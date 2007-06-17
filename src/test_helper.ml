open OUnit
open Lppterm

(* Parsing functions *)

let parse_term str =
  Parser.term Lexer.token (Lexing.from_string str)

let parse_obj str =
  Parser.contexted_term Lexer.token (Lexing.from_string str)

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

let assert_string_equal = assert_equal ~printer:(fun s -> s)

let assert_pprint_equal s t =
  assert_equal ~printer:id s (lppterm_to_string t)

let assert_int_equal = assert_equal ~printer:string_of_int

let assert_string_list_equal lst1 lst2 =
  assert_int_equal (List.length lst1) (List.length lst2) ;
  ignore (List.map2 assert_string_equal lst1 lst2)

let assert_raises_any ?msg (f: unit -> 'a) =
  let str = "expected exception, but no exception was raised." in
    match raises f, msg with
      | Some e, _ -> ()
	  | None, None -> assert_failure str
	  | None, Some s -> assert_failure (Format.sprintf "%s\n%s" s str)

