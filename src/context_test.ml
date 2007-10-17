open OUnit
open Test_helper
open Context
open Metaterm
open Unify

let assert_true b = assert_bool "" b
let assert_false b = assert_bool "" (not b)

let evalAB = Term.app (Term.const "eval") [Term.const "A"; Term.const "B"]
let varL = Term.var Term.Logic "L" 0

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

    "Context membership should be based on equality modulo pointers" >::
      (fun () ->
         let ctx = add evalAB empty in
         let var = Term.var Term.Logic "X" 0 in
           right_unify var evalAB ;
           assert_true (mem var ctx)) ;

    "Remove should be based on equality modulo pointers" >::
      (fun () ->
         let ctx = add evalAB empty in
         let var = Term.var Term.Logic "X" 0 in
           right_unify var evalAB ;
           let ctx' = remove var ctx in
             assert_true (is_empty ctx')) ;

    "Xor should remove matching elements" >::
      (fun () ->
         let a = Term.const "A" in
         let b = Term.const "B" in
         let c = Term.const "C" in
         let d = Term.const "D" in
         let ctx1 = add a (add b (add c empty)) in
         let ctx2 = add b (add d empty) in
         let ctx1', ctx2' = xor ctx1 ctx2 in
           assert_true (mem a ctx1') ;
           assert_false (mem b ctx1') ;
           assert_true (mem c ctx1') ;
           assert_false (mem b ctx2') ;
           assert_true (mem d ctx2')) ;

    "Group utility" >::
      (fun () ->
         let a = Term.const "A" in
         let b = Term.const "B" in
         let result = group [(a, 1); (b, 2); (a, 3); (a, 4)] in
           assert_equal [(a, [1; 3; 4]); (b, [2])] result) ;

    "Context to term without context variable" >::
      (fun () ->
         let a = Term.const "A" in
         let b = Term.const "B" in
         let ctx = add a (add b empty) in
           assert_term_pprint_equal
             "A :: B :: nil" (context_to_term ctx)) ;
    
    "Context to term with context variable" >::
      (fun () ->
         let a = Term.const "A" in
         let b = Term.const "B" in
         let l = Term.var Term.Eigen "L" 0 in
         let ctx = add a (add b (add l empty)) in
           assert_term_pprint_equal
             "A :: B :: L" (context_to_term ctx)) ;

    "Normalize should remove duplicates" >::
      (fun () ->
         let a = Term.const "A" in
         let b = Term.const "B" in
         let ctx = add a (add b (add a empty)) in
         let ctx = Context.normalize ctx in
           assert_equal 2 (size ctx));

    "Normalize should replace cons with seperate elements" >::
      (fun () ->
         let a = Term.const "A" in
         let l = Term.var Term.Eigen "L" 0 in
         let term = Term.app cons [a; l] in
         let ctx = Context.normalize (add term empty) in
           assert_true (mem a ctx) ;
           assert_true (mem l ctx)) ;

    "Normalize should replace nil with nothing" >::
      (fun () ->
         let l = Term.var Term.Eigen "L" 0 in
         let ctx = add l empty in
           left_unify l (Term.const "nil") ;
           assert_true (is_empty (Context.normalize ctx))) ;

    "Reconcile should produce subcontexts" >::
      (fun () ->
         let a = Term.const "A" in
         let b = Term.const "B" in
         let c = Term.const "C" in
         let d = Term.const "D" in
         let l = Term.var Term.Eigen "L" 0 in
         let e = Term.var Term.Logic "E" 0 in
         let ctx1 = add a (add e empty) in
         let ctx2 = add c (add b (add a (add l empty))) in
         let ctx3 = add e empty in
         let ctx4 = add d (add l empty) in
           reconcile [(ctx1, ctx2); (ctx3, ctx4)] ;
           let ctx3' = Context.normalize ctx3 in
             assert_equal 4 (size ctx3') ;
             assert_true (mem l ctx3') ;
             assert_true (mem b ctx3') ;
             assert_true (mem c ctx3') ;
             assert_true (mem d ctx3')) ;
  ]
