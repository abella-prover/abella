open OUnit
open Metaterm
open Extensions
open Typing
open Accumulate
open Abella_types

(* We make use of the global prover signature 'sign' to simply testing *)
open Prover

(* Parsing functions *)

let parse_uterm str =
  Parser.term Lexer.token (Lexing.from_string str)

let parse_umetaterm str =
  Parser.metaterm Lexer.token (Lexing.from_string str)

let parse_top_command str =
  Parser.top_command Lexer.token (Lexing.from_string str)

let parse_metaterm ?(ctx=[]) str =
  type_umetaterm ~sr:!sr ~sign:!sign ~ctx (parse_umetaterm str)

let parse_uclauses str =
  Parser.mod_body Lexer.token (Lexing.from_string str)

let parse_clauses str =
  List.map (type_uclause ~sr:!sr ~sign:!sign) (parse_uclauses str)

let parse_decls str =
  Parser.sig_body Lexer.token (Lexing.from_string str)

let parse_udefs str =
  Parser.defs Lexer.token (Lexing.from_string str)

let parse_defs str =
  type_udefs ~sr:!sr ~sign:!sign (parse_udefs str) |>
  List.map (fun (head, body) -> ({head = head; body = body}))

let eval_sig_string = "\
  kind      tm        type.\
  type      app       tm -> tm -> tm.\
  type      abs       (tm -> tm) -> tm.\
\
  kind      ty        type.\
  type      arrow     ty -> ty -> ty.\
\
  type      typeof    tm -> ty -> o.\
  type      eval      tm -> tm -> o."

let eval_clauses_string = "\
  typeof (abs R) (arrow T U) :- pi x\\ (typeof x T => typeof (R x) U).\
  typeof (app M N) T :- typeof M (arrow U T), typeof N U.\
  eval (abs R) (abs R).\
  eval (app M N) V :- eval M (abs R), eval (R N) V."

let process_decls decls =
  sign := List.fold_left add_decl !sign decls ;
  sr := List.fold_left Subordination.update !sr
    (List.filter_map
       (function Abella_types.SType(_, ty) -> Some ty | _ -> None)
       decls)

let () = process_decls (parse_decls eval_sig_string)

let eval_clauses = parse_clauses eval_clauses_string

let extra_sig_string = "\
  kind       i                     type.\
\
  type       t1, t2, t3, t4        i.\
  type       r1, r2                i -> i.\
\
  type       iabs                  (i -> i) -> i.\
  type       iapp                  i -> i -> i.\
\
  type       a, b, c, d            o.\
  type       p1, p2, p3            i -> o.\
  type       hyp, conc, form       i -> o.\
\
  type       eq, pr                i -> i -> o."

let () = process_decls (parse_decls extra_sig_string)

let nat_sig_string = "\
  kind       nat                  type.\
\
  type       z                    nat.\
  type       s                    nat -> nat.\
\
  type       nat, even, odd       nat -> o.\
  type       add                  nat -> nat -> nat -> o."

let () = process_decls (parse_decls nat_sig_string)

let process_top_command str =
  match parse_top_command str with
    | Abella_types.Kind(ids, knd) ->
        add_global_types ids knd ;
    | Abella_types.Type(ids, ty) ->
        add_global_consts (List.map (fun id -> (id, ty)) ids)
    | Abella_types.Close(ids) ->
        close_types !sign !clauses ids
    | _ -> assert false

let () = process_top_command "Type   foo, bar, baz         i -> prop."
let () = process_top_command "Type   rel1, rel2, rel3      i -> i -> prop."
let () = process_top_command "Type   ctx                   olist -> prop."

(* For subordination tests *)
let () = process_top_command "Kind     sr_a, sr_b     type."
let () = process_top_command "Type     a_to_b   sr_a -> sr_b."
let () = process_top_command "Type     sr_a_b   sr_a -> sr_b -> prop."
let () = process_top_command "Close    sr_a, sr_b."
let sr_a = Term.tybase (Term.atybase "sr_a")
let sr_b = Term.tybase (Term.atybase "sr_b")
let sr_sr =
  Subordination.close
    (Subordination.update Subordination.empty (Term.tyarrow [sr_a] sr_b))
    [Term.atybase "sr_a"; Term.atybase "sr_b"]

let freshen str =
  let uterm = parse_umetaterm str in
  let fv =
    ids_to_fresh_tyctx (umetaterm_extract_if Term.is_capital_name uterm)
  in
  let ctx = fresh_alist ~tag:Term.Eigen ~used:[] fv in
  match
    type_umetaterm ~sr:!sr ~sign:!sign ~ctx
      (UBinding(Metaterm.Forall, fv, uterm))
  with
    | Binding(Metaterm.Forall, fv, body) ->
        let ctx = fresh_alist ~tag:Term.Eigen ~used:[] fv in
          replace_metaterm_vars ctx body
    | t -> t

(* Custom asserts *)

let assert_true b = assert_bool "Expected true" b
let assert_false b = assert_bool "Expected false" (not b)

let assert_string_equal =
  assert_equal ~printer:(fun s -> s)

let renumber_term t =
  let rec spin dep t =
    match Term.observe (Term.hnorm t) with
    | Term.Var _ | Term.DB _ -> t
    | Term.Lam (tycx, t) ->
        let (dep, tycx) = List.fold_left begin
          fun (dep, tycx) (_, ty) ->
            let xv = "x" ^ string_of_int dep in
            let dep = dep + 1 in
            let tycx = (xv, ty) :: tycx in
            (dep, tycx)
        end (dep, []) tycx in
        let tycx = List.rev tycx in
        let t = spin dep t in
        Term.lambda tycx t
    | Term.App (f, ts) ->
        let f = spin dep f in
        let ts = List.map (spin dep) ts in
        Term.app f ts
    | Term.Susp _ | Term.Ptr _ -> assert false
  in
  spin 1 t

let assert_pprint_equal s t =
  let t = map_terms renumber_term t in
  assert_string_equal s (metaterm_to_string t)

let assert_metaterm_equal s t =
  let s = map_terms renumber_term s in
  let t = map_terms renumber_term t in
  assert_string_equal (metaterm_to_string s) (metaterm_to_string t)

let assert_term_pprint_equal s t =
  let t = renumber_term t in
  assert_string_equal s (Term.term_to_string t)

let assert_term_pprint_differeent s t =
  let t = renumber_term t in
  assert_string_equal s (Term.term_to_string t)

let assert_ty_pprint_equal s t =
  assert_string_equal s (Term.ty_to_string t)

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
      | Some _, _ -> ()
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

let ity = Term.tybase (Term.atybase "i")
let iity = Term.tyarrow [ity] ity
let iiity = Term.tyarrow [ity; ity] ity
let iiiity = Term.tyarrow [ity; ity; ity] ity

let aty = Term.tybase (Term.atybase "a")
let bty = Term.tybase (Term.atybase "b")
let cty = Term.tybase (Term.atybase "c")
let dty = Term.tybase (Term.atybase "d")
let ety = Term.tybase (Term.atybase "e")

(* We can ignore types for some tests *)

let emptyty = Term.tybase (Term.atybase "")
let uconst name = Term.const name emptyty
let uvar tag name ts = Term.var tag name ts emptyty
let unominal_var name = Term.nominal_var name emptyty
let (///) n t = Term.lambda (List.replicate n ("x",emptyty)) t
