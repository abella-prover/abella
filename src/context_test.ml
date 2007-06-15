open OUnit
open Test_helper
open Context
open Lppterm

let assert_true b = assert_bool "" b
let assert_false b = assert_bool "" (not b)

let term = Term.app (Term.const "eval") [Term.const "A"; Term.const "B"]
let ctx_var = var "L"

let tests =
  "Context" >::: [
    "Empty context should have no members" >::
      (fun () ->
         assert_false (mem_term term empty)) ;

    "Empty context should be empty" >::
      (fun () ->
         assert_true (is_empty empty)) ;

    "Singleton context should not be empty" >::
      (fun () ->
         let ctx = add_term term empty in
           assert_false (is_empty ctx)) ;

    "Add term to context" >::
      (fun () ->
         let ctx = add_term term empty in
           assert_true (mem_term term ctx)) ;

    "Add to context variable to context" >::
      (fun () ->
         let ctx = add ctx_var empty in
           assert_true (mem ctx_var ctx)) ;

    "Add term and variable to context" >::
      (fun () ->
         let ctx = add ctx_var (add_term term empty) in
           assert_true (mem ctx_var ctx) ;
           assert_true (mem_term term ctx)) ;

    "Print variables before terms" >::
      (fun () ->
         let ctx = add ctx_var (add_term term empty) in
           assert_string_equal "L, eval A B" (context_to_string ctx)) ;

  ]
