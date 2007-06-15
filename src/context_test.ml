open OUnit
open Test_helper
open Context
open Lppterm

let assert_true b = assert_bool "" b
let assert_false b = assert_bool "" (not b)

let evalAB = Term.app (Term.const "eval") [Term.const "A"; Term.const "B"]
let varL = Term.var "L" 0

let tests =
  "Context" >::: [
    "Empty context should have no members" >::
      (fun () ->
         assert_false (mem evalAB empty)) ;

    "Empty context should be empty" >::
      (fun () ->
         assert_true (is_empty empty)) ;

    "Singleton context should not be empty" >::
      (fun () ->
         let ctx = add evalAB empty in
           assert_false (is_empty ctx)) ;

    "Added term should be a member" >::
      (fun () ->
         let ctx = add evalAB empty in
           assert_true (mem evalAB ctx)) ;

    "Print context" >::
      (fun () ->
         let ctx = add evalAB (add varL empty) in
           assert_string_equal "L, eval A B" (context_to_string ctx)) ;

    "Empty context should be subcontext of empty context" >::
      (fun () ->
         assert_true (subcontext empty empty)) ;

    "Empty context should be subcontext of singleton context" >::
      (fun () ->
         let ctx = add evalAB empty in
           assert_true (subcontext empty ctx)) ;

    "Singleton context should be subcontext of itself" >::
      (fun () ->
         let ctx = add evalAB empty in
           assert_true (subcontext ctx ctx)) ;
         
    "Singleton context should not be subcontext of empty context" >::
      (fun () ->
         let ctx = add evalAB empty in
           assert_false (subcontext ctx empty)) ;
  ]
