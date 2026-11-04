open Abella_lib
open Term
open Metaterm
open Test_helper

module R = Abella_driver.Replacement

let nat = tybase (atybase "nat")
let nat_prop = tyarrow [nat] propty
let p = const "p" nat_prop
let q = const "q" nat_prop

let replacement decl defn =
  let target = { R.name = term_to_name defn ; term = defn ; ty = tc [] defn } in
  { R.map = Itab.singleton decl target ;
    R.range = Iset.singleton target.R.name }

let apply body = R.metaterm (replacement "p" q) body

let pred_p x = Pred (app p [x], Irrelevant)

let tests =
  suite "Replacement" [
      test_case "Replacement is applied to a predicate atom"
        (fun () ->
           let a = const "a" nat in
           let mt = pred_p a in
             assert_pprint_equal "q a" (apply mt)) ;

      test_case "Forall binder avoids capture by the replacement"
        (fun () ->
           let bound_q = const "q" nat in
           let mt = forall [("q", nat)] (pred_p bound_q) in
             assert_pprint_equal "forall q1, q q1" (apply mt)) ;

      test_case "A binder with the replacement key is not replaced"
        (fun () ->
           let bound_p = const "p" nat in
           let mt = forall [("p", nat)] (pred_p bound_p) in
             assert_pprint_equal "forall p, p p" (apply mt)) ;

      test_case "Term lambda keeps the replacement constant free"
        (fun () ->
           let lam = lambda [("q", nat)] (app p [db 1]) in
           let mt = Eq(lam, lam) in
             match apply mt with
             | Eq(t, _) ->
                 Alcotest.check Alcotest.string "term printing"
                   "q1\\q q1" (term_to_string t)
             | _ -> Alcotest.fail "expected an equation") ;
    ]
