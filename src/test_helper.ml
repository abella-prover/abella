open OUnit
open Metaterm

(* Parsing functions *)

let parse_term str =
  Parser.term Lexer.token (Lexing.from_string str)

let parse_obj str =
  Parser.contexted_term Lexer.token (Lexing.from_string str)

let parse_metaterm str =
  Parser.metaterm Lexer.token (Lexing.from_string str)

let parse_clauses str =
  Parser.clauses Lexer.token (Lexing.from_string str)

let parse_meta_clauses str =
  Parser.meta_clauses Lexer.token (Lexing.from_string str)

let read_mod filename =
  Parser.clauses Lexer.token (Lexing.from_channel (open_in filename))

let freshen str =
  let term = parse_metaterm str in
  let var_names = Tactics.capital_var_names (collect_terms term) in
  let fresh_names = fresh_alist ~tag:Term.Eigen ~used:[] var_names in
    replace_metaterm_vars fresh_names term

let make_nominals list term =
  let alist = List.map (fun x -> (x, Term.nominal_var x)) list in
    replace_metaterm_vars alist term
               
let eval_clauses = read_mod "eval.mod"
let fsub_clauses = read_mod "fsub.mod"
let addition_clauses = read_mod "add.mod"
  
(* Custom asserts *)
    
let assert_string_equal =
  assert_equal ~printer:(fun s -> s)

let assert_pprint_equal s t =
  assert_string_equal s (metaterm_to_string t)

let assert_term_pprint_equal s t =
  assert_string_equal s (Term.term_to_string t)

let assert_term_equal =
  assert_equal ~cmp:Term.full_eq ~printer:Term.term_to_string

let assert_int_equal =
  assert_equal ~printer:string_of_int

let assert_string_list_equal lst1 lst2 =
  assert_int_equal (List.length lst1) (List.length lst2) ;
  ignore (List.map2 assert_string_equal lst1 lst2)

let assert_raises_any ?msg (f: unit -> 'a) =
  let str = "expected exception, but no exception was raised." in
    match raises f, msg with
      | Some e, _ -> ()
	  | None, None -> assert_failure str
	  | None, Some s -> assert_failure (Format.sprintf "%s\n%s" s str)

