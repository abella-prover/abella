open Test_helper
open Abella_lib
open Context
open Unify
open Term
open Term.Notations

let tmty = tybase (atybase "tm")
let eval = const "eval" (tyarrow [tmty; tmty] oty)
let evalAB = eval ^^ [const "A" tmty; const "B" tmty]

let tests =
  suite "Context" [
    test_case "Empty context should have no members"
      (fun () ->
         Alcotest.check Alcotest.bool "expected false" false (mem evalAB empty)) ;

    test_case "Empty context should be empty"
      (fun () ->
         Alcotest.check Alcotest.bool "expected true" true (is_empty empty)) ;

    test_case "Singleton context should not be empty"
      (fun () ->
         let ctx = add evalAB empty in
           Alcotest.check Alcotest.bool "expected false" false (is_empty ctx)) ;

    test_case "Added term should be a member"
      (fun () ->
         let ctx = add evalAB empty in
           Alcotest.check Alcotest.bool "expected true" true (mem evalAB ctx)) ;

    test_case "Print context"
      (fun () ->
         let l = var Logic "L" 0 olistty in
         let ctx = add evalAB (add l empty) in
           Alcotest.check Alcotest.string "strings differ" "L, eval A B" (context_to_string ctx)) ;

    test_case "Empty context should be subcontext of empty context"
      (fun () ->
         Alcotest.check Alcotest.bool "expected true" true (subcontext empty empty)) ;

    test_case "Empty context should be subcontext of singleton context"
      (fun () ->
         let ctx = add evalAB empty in
           Alcotest.check Alcotest.bool "expected true" true (subcontext empty ctx)) ;

    test_case "Singleton context should be subcontext of itself"
      (fun () ->
         let ctx = add evalAB empty in
           Alcotest.check Alcotest.bool "expected true" true (subcontext ctx ctx)) ;

    test_case "Singleton context should not be subcontext of empty context"
      (fun () ->
         let ctx = add evalAB empty in
           Alcotest.check Alcotest.bool "expected false" false (subcontext ctx empty)) ;

    test_case "Context membership should be based on equality modulo pointers"
      (fun () ->
         let ctx = add evalAB empty in
         let var = var Logic "X" 0 oty in
           right_unify var evalAB ;
           Alcotest.check Alcotest.bool "expected true" true (mem var ctx)) ;

    test_case "Remove should be based on equality modulo pointers"
      (fun () ->
         let ctx = add evalAB empty in
         let var = var Logic "X" 0 oty in
           right_unify var evalAB ;
           let ctx' = remove var ctx in
             Alcotest.check Alcotest.bool "expected true" true (is_empty ctx')) ;

    test_case "Remove should be based on unification"
      (fun () ->
         let e = var Eigen "E" 0 (tyarrow [tmty] tmty) in
         let abs = const "abs" (tyarrow [tmty] tmty) in
         let eval_abs1 = eval ^^ [abs ^^ [1 /// (e ^^ [db 1])]] in
         let eval_abs2 = eval ^^ [abs ^^ [e]] in
         let ctx = add eval_abs1 empty in
           let ctx' = remove eval_abs2 ctx in
             Alcotest.check Alcotest.bool "expected true" true (is_empty ctx')) ;

    test_case "Xor should remove matching elements"
      (fun () ->
         let a = const "A" oty in
         let b = const "B" oty in
         let c = const "C" oty in
         let d = const "D" oty in
         let ctx1 = add a (add b (add c empty)) in
         let ctx2 = add b (add d empty) in
         let ctx1', ctx2' = xor ctx1 ctx2 in
           Alcotest.check Alcotest.bool "expected true" true (mem a ctx1') ;
           Alcotest.check Alcotest.bool "expected false" false (mem b ctx1') ;
           Alcotest.check Alcotest.bool "expected true" true (mem c ctx1') ;
           Alcotest.check Alcotest.bool "expected false" false (mem b ctx2') ;
           Alcotest.check Alcotest.bool "expected true" true (mem d ctx2')) ;

    test_case "Group utility"
      (fun () ->
         let a = const "A" oty in
         let b = const "B" oty in
         let result = group [(a, 1); (b, 2); (a, 3); (a, 4)] in
           Alcotest.check
             (Alcotest.list
                (Alcotest.pair term_testable (Alcotest.list Alcotest.int)))
             "grouped context" [(a, [1; 3; 4]); (b, [2])] result) ;

    test_case "Context to term without context variable"
      (fun () ->
         let a = const "a" oty in
         let b = const "b" oty in
         let ctx = add a (add b empty) in
           assert_term_pprint_equal
             "a :: b :: nil" (context_to_term ctx)) ;

    test_case "Context to term with context variable"
      (fun () ->
         let a = const "a" oty in
         let b = const "b" oty in
         let l = var Eigen "L" 0 olistty in
         let ctx = add a (add b (add l empty)) in
           assert_term_pprint_equal
             "a :: b :: L" (context_to_term ctx)) ;

    test_case "Context to term with context variable raised"
      (fun () ->
         let l = var Eigen "L" 0 (tyarrow [ity] olistty) in
         let n = nominal_var "n" ity in
         let ctx = add (l ^^ [n]) empty in
           assert_term_pprint_equal
             "L n" (context_to_term ctx)) ;

    test_case "Normalize should remove duplicates"
      (fun () ->
         let a = const "A" oty in
         let b = const "B" oty in
         let ctx = add a (add b (add a empty)) in
         let ctx = Context.normalize ctx in
           Alcotest.check Alcotest.int "context size" 2 (size ctx));

    test_case "Normalize should replace cons with seperate elements"
      (fun () ->
         let a = const "A" oty in
         let l = var Eigen "L" 0 olistty in
         let term = cons ^^ [a; l] in
         let ctx = Context.normalize (add term empty) in
           Alcotest.check Alcotest.bool "expected true" true (mem a ctx) ;
           Alcotest.check Alcotest.bool "expected true" true (mem l ctx)) ;

    test_case "Normalize should replace nil with nothing"
      (fun () ->
         let l = var Eigen "L" 0 olistty in
         let ctx = add l empty in
           left_unify l nil ;
           Alcotest.check Alcotest.bool "expected true" true (is_empty (Context.normalize ctx))) ;

    test_case "Reconcile should produce subcontexts"
      (fun () ->
         let a = const "A" oty in
         let b = const "B" oty in
         let c = const "C" oty in
         let d = const "D" oty in
         let l = var Eigen "L" 0 olistty in
         let e = var Logic "E" 0 olistty in
         let ctx1 = add a (add e empty) in
         let ctx2 = add c (add b (add a (add l empty))) in
         let ctx3 = add e empty in
         let ctx4 = add d (add l empty) in
           reconcile [(ctx1, ctx2); (ctx3, ctx4)] ;
           let ctx3' = Context.normalize ctx3 in
             Alcotest.check Alcotest.int "context size" 4 (size ctx3') ;
             Alcotest.check Alcotest.bool "expected true" true (mem l ctx3') ;
             Alcotest.check Alcotest.bool "expected true" true (mem b ctx3') ;
             Alcotest.check Alcotest.bool "expected true" true (mem c ctx3') ;
             Alcotest.check Alcotest.bool "expected true" true (mem d ctx3')) ;

  ]
