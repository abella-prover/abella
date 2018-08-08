open OUnit
open Test_helper
open Context
open Unify
open Term
open Term.Notations

let tmty = tybase (atybase "tm")
let eval = const "eval" (tyarrow [tmty; tmty] oty)
let evalAB = eval ^^ [const "A" tmty; const "B" tmty]

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
         let l = var Logic "L" 0 olistty in
         let ctx = add evalAB (add l empty) in
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
         let var = var Logic "X" 0 oty in
           right_unify var evalAB ;
           assert_true (mem var ctx)) ;

    "Remove should be based on equality modulo pointers" >::
      (fun () ->
         let ctx = add evalAB empty in
         let var = var Logic "X" 0 oty in
           right_unify var evalAB ;
           let ctx' = remove var ctx in
             assert_true (is_empty ctx')) ;

    "Remove should be based on unification" >::
      (fun () ->
         let e = var Eigen "E" 0 (tyarrow [tmty] tmty) in
         let abs = const "abs" (tyarrow [tmty] tmty) in
         let eval_abs1 = eval ^^ [abs ^^ [1 /// (e ^^ [db 1])]] in
         let eval_abs2 = eval ^^ [abs ^^ [e]] in
         let ctx = add eval_abs1 empty in
           let ctx' = remove eval_abs2 ctx in
             assert_true (is_empty ctx')) ;

    "Xor should remove matching elements" >::
      (fun () ->
         let a = const "A" oty in
         let b = const "B" oty in
         let c = const "C" oty in
         let d = const "D" oty in
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
         let a = const "A" oty in
         let b = const "B" oty in
         let result = group [(a, 1); (b, 2); (a, 3); (a, 4)] in
           assert_equal [(a, [1; 3; 4]); (b, [2])] result) ;

    "Context to term without context variable" >::
      (fun () ->
         let a = const "a" oty in
         let b = const "b" oty in
         let ctx = add a (add b empty) in
           assert_term_pprint_equal
             "a :: b :: nil" (context_to_term ctx)) ;

    "Context to term with context variable" >::
      (fun () ->
         let a = const "a" oty in
         let b = const "b" oty in
         let l = var Eigen "L" 0 olistty in
         let ctx = add a (add b (add l empty)) in
           assert_term_pprint_equal
             "a :: b :: L" (context_to_term ctx)) ;

    "Context to term with context variable raised" >::
      (fun () ->
         let l = var Eigen "L" 0 (tyarrow [ity] olistty) in
         let n = nominal_var "n" ity in
         let ctx = add (l ^^ [n]) empty in
           assert_term_pprint_equal
             "L n" (context_to_term ctx)) ;

    "Normalize should remove duplicates" >::
      (fun () ->
         let a = const "A" oty in
         let b = const "B" oty in
         let ctx = add a (add b (add a empty)) in
         let ctx = Context.normalize ctx in
           assert_equal 2 (size ctx));

    "Normalize should replace cons with seperate elements" >::
      (fun () ->
         let a = const "A" oty in
         let l = var Eigen "L" 0 olistty in
         let term = cons ^^ [a; l] in
         let ctx = Context.normalize (add term empty) in
           assert_true (mem a ctx) ;
           assert_true (mem l ctx)) ;

    "Normalize should replace nil with nothing" >::
      (fun () ->
         let l = var Eigen "L" 0 olistty in
         let ctx = add l empty in
           left_unify l nil ;
           assert_true (is_empty (Context.normalize ctx))) ;

    "Reconcile should produce subcontexts" >::
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
             assert_equal 4 (size ctx3') ;
             assert_true (mem l ctx3') ;
             assert_true (mem b ctx3') ;
             assert_true (mem c ctx3') ;
             assert_true (mem d ctx3')) ;

  ]
