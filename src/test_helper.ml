open OUnit
open Metaterm
open Extensions
open Typing

(* Parsing functions *)

let parse_uterm str =
  Parser.term Lexer.token (Lexing.from_string str)

let parse_umetaterm str =
  Parser.metaterm Lexer.token (Lexing.from_string str)

let parse_top_command str =
  Parser.top_command Lexer.token (Lexing.from_string str)

let parse_metaterm ?(ctx=[]) str =
  type_umetaterm ~ctx (parse_umetaterm str)

let parse_ulpmod str =
  Parser.lpmod Lexer.token (Lexing.from_string str)

let parse_lpmod str =
  List.map type_uclause (parse_ulpmod str)

let parse_lpsig str =
  Parser.lpsig Lexer.token (Lexing.from_string str)

let parse_udefs str =
   Parser.defs Lexer.token (Lexing.from_string str)

let parse_defs str =
  type_udefs (parse_udefs str)

let eval_sig_string = "
  kind      tm        type.
  type      app       tm -> tm -> tm.
  type      abs       (tm -> tm) -> tm.

  kind      ty        type.
  type      arrow     ty -> ty -> ty.

  type      typeof    tm -> ty -> o.
  type      eval      tm -> tm -> o."

let eval_clauses_string = "
  typeof (abs R) (arrow T U) :- pi x\\ (typeof x T => typeof (R x) U).
  typeof (app M N) T :- typeof M (arrow U T), typeof N U.
  eval (abs R) (abs R).
  eval (app M N) V :- eval M (abs R), eval (R N) V."

let eval_clauses =
  parse_lpsig eval_sig_string ;
  parse_lpmod eval_clauses_string

let extra_sig_string = "
  kind       i                     type.

  type       t1, t2, t3, t4        i.
  type       r1, r2                i -> i.

  type       iabs                  (i -> i) -> i.
  type       iapp                  i -> i -> i.

  type       a, b, c, d            o.
  type       p1, p2, p3            i -> o.
  type       hyp, conc, form       i -> o.

  type       eq, pr                i -> i -> o."

let _ = parse_lpsig extra_sig_string

let nat_sig_string = "
  kind       nat                  type.

  type       z                    nat.
  type       s                    nat -> nat.

  type       nat, even, odd       nat -> o.
  type       add                  nat -> nat -> nat -> o."

let _ = parse_lpsig nat_sig_string

let _ = parse_top_command "Type   foo, bar, baz         i -> prop."
let _ = parse_top_command "Type   rel1, rel2, rel3      i -> i -> prop."
let _ = parse_top_command "Type   ctx                   olist -> prop."

let freshen str =
  let uterm = parse_umetaterm str in
  let fv =
    ids_to_fresh_tyctx (umetaterm_extract_if Term.is_capital_name uterm)
  in
  let ctx = fresh_alist ~tag:Term.Eigen ~used:[] fv in
  match type_umetaterm ~ctx (UBinding(Metaterm.Forall, fv, uterm)) with
    | Binding(Metaterm.Forall, fv, body) ->
        let ctx = fresh_alist ~tag:Term.Eigen ~used:[] fv in
          replace_metaterm_vars ctx body
    | _ -> assert false

(* Custom asserts *)

let assert_string_equal =
  assert_equal ~printer:(fun s -> s)

let assert_pprint_equal s t =
  assert_string_equal s (metaterm_to_string t)

let assert_metaterm_equal s t =
  assert_string_equal (metaterm_to_string s) (metaterm_to_string t)

let assert_term_pprint_equal s t =
  assert_string_equal s (Term.term_to_string t)

let assert_term_equal =
  assert_equal ~cmp:Term.eq ~printer:Term.term_to_string

let assert_ty_equal =
  assert_equal ~printer:Term.ty_to_string

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

let rec extract_tests path test =
  match path, test with
    | [], _ -> test
    | n::rest, TestList l ->
        TestLabel(string_of_int n, extract_tests rest (List.nth l n))
    | _, TestLabel(name, t) ->
        TestLabel(name, extract_tests path t)
    | _ -> assert false

(* Quick types *)

let ity = Term.tybase "i"
let iity = Term.tyarrow [ity] ity
let iiity = Term.tyarrow [ity; ity] ity
let iiiity = Term.tyarrow [ity; ity; ity] ity

let aty = Term.tybase "a"
let bty = Term.tybase "b"
let cty = Term.tybase "c"
let dty = Term.tybase "d"
let ety = Term.tybase "e"

(* We can ignore types for some tests *)

let emptyty = Term.tybase ""
let uconst name = Term.const name emptyty
let uvar tag name ts = Term.var tag name ts emptyty
let unominal_var name = Term.nominal_var name emptyty
let (///) n t = Term.lambda (List.replicate n emptyty) t
