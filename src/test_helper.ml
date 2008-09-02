open OUnit
open Metaterm
open Extensions

(* Parsing functions *)

let parse_term str =
  Parser.term Lexer.token (Lexing.from_string str)

let parse_obj str =
  Parser.contexted_term Lexer.token (Lexing.from_string str)

let parse_metaterm str =
  Parser.metaterm Lexer.token (Lexing.from_string str)

let parse_clauses str =
  Parser.clauses Lexer.token (Lexing.from_string str)

let parse_defs str =
  Parser.defs Lexer.token (Lexing.from_string str)

let freshen str =
  let term = parse_metaterm str in
  let fresh_eigen_names =
    term
    |> collect_terms
    |> Tactics.capital_var_names
    |> fresh_alist ~tag:Term.Eigen ~used:[]
  in
  let fresh_logic_names =
    term
    |> collect_terms
    |> Tactics.question_var_names
    |> fresh_alist ~tag:Term.Logic ~used:[]
  in
    term
    |> replace_metaterm_vars fresh_eigen_names
    |> replace_metaterm_vars fresh_logic_names
    |> replace_metaterm_nominal_vars

let eval_clauses_string = "
  typeof (abs R) (arrow T U) :- pi x\\ (typeof x T => typeof (R x) U).
  typeof (app M N) T :- typeof M (arrow U T), typeof N U.
  eval (abs R) (abs R).
  eval (app M N) V :- eval M (abs R), eval (R N) V."

let eval_clauses = parse_clauses eval_clauses_string

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

