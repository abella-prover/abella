open OUnit
open Term
open Term.Notations
open Lppterm
open Tactics
  
let id x = x
  
let assert_pprint_equal s t =
  assert_equal ~printer:id s (lppterm_to_string t)

let parse str = Parser.lppterm Lexer.token (Lexing.from_string str)
    
let tests =
  "Tactics" >:::
    [
      "Simple object cut" >::
        (fun () ->
           let t = object_cut (parse "{A => B}") (parse "{A}") in
             assert_pprint_equal "{B}" t) ;
      
      "Compound object cut" >::
        (fun () ->
           let h0 = parse "{eval A B => typeof B C}" in
           let h1 = parse "{eval A B}" in
           let t = object_cut h0 h1 in
             assert_pprint_equal "{typeof B C}" t) ;

      "Simple object instantiation" >::
        (fun () ->
           let h0 = parse "{pi x\\ eval x B}" in
           let a = atom "A" in
           let t = object_inst h0 a in
             assert_pprint_equal "{eval A B}" t) ;

      "Forall application" >::
        (fun () ->
           let h0 = parse ("forall (A : tm) (B : tm) (C : ty), " ^
                             "{eval A B} -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}" in
           let h2 = parse "{typeof (abs R) (arrow S T)}" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Properly restricted forall application" >::
        (fun () ->
           (* We have to construct this manually because the parser does
              not understand restrictions.
              
              forall (A : tm) (B : tm) (C : ty),
                {eval A B}* -> {typeof A C} -> {typeof B C}
              instantiated with {eval (abs R) (abs R)}*
                                {typeof (abs R) (arrow S T)} *)
           let a = atom "A" in
           let b = atom "B" in
           let c = atom "C" in
           let tm = atom "tm" in
           let ty = atom "ty" in
           let evalAB = active_obj (app (atom "eval") [a; b]) 1 in
           let typeofAC = obj (app (atom "typeof") [a; c]) in
           let typeofBC = obj (app (atom "typeof") [b; c]) in
           let stmt = forall [("A", tm); ("B", tm); ("C", ty)]
             (arrow evalAB (arrow typeofAC typeofBC)) in
           let absR = app (atom "abs") [var ~tag:Eigen "R" 0] in
           let evalabsR = active_obj (app (atom "eval") [absR; absR]) 1 in
           let arrowST = app (atom "arrow") [var ~tag:Eigen "S" 0;
                                             var ~tag:Eigen "T" 0] in
           let typeofabsR = obj (app (atom "typeof") [absR; arrowST]) in
           let t = apply_forall stmt [evalabsR; typeofabsR] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Needlessly restricted forall application" >::
        (fun () ->
           (* We have to construct this manually because the parser does
              not understand restrictions.
              
              forall (A : tm) (B : tm) (C : ty),
                {eval A B} -> {typeof A C} -> {typeof B C}
              instantiated with {eval (abs R) (abs R)}*
                                {typeof (abs R) (arrow S T)} *)
           let a = atom "A" in
           let b = atom "B" in
           let c = atom "C" in
           let tm = atom "tm" in
           let ty = atom "ty" in
           let evalAB = obj (app (atom "eval") [a; b]) in
           let typeofAC = obj (app (atom "typeof") [a; c]) in
           let typeofBC = obj (app (atom "typeof") [b; c]) in
           let stmt = forall [("A", tm); ("B", tm); ("C", ty)]
             (arrow evalAB (arrow typeofAC typeofBC)) in
           let absR = app (atom "abs") [var ~tag:Eigen "R" 0] in
           let evalabsR = active_obj (app (atom "eval") [absR; absR]) 1 in
           let arrowST = app (atom "arrow") [var ~tag:Eigen "S" 0;
                                             var ~tag:Eigen "T" 0] in
           let typeofabsR = obj (app (atom "typeof") [absR; arrowST]) in
           let t = apply_forall stmt [evalabsR; typeofabsR] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;
      
      "Improperly restricted forall application" >::
        (fun () ->
           (* We have to construct this manually because the parser does
              not understand restrictions.
              
              forall (A : tm) (B : tm) (C : ty),
                {eval A B}* -> {typeof A C} -> {typeof B C}
              instantiated with {eval (abs R) (abs R)}
                                {typeof (abs R) (arrow S T)} *)
           let a = atom "A" in
           let b = atom "B" in
           let c = atom "C" in
           let tm = atom "tm" in
           let ty = atom "ty" in
           let evalAB = active_obj (app (atom "eval") [a; b]) 1 in
           let typeofAC = obj (app (atom "typeof") [a; c]) in
           let typeofBC = obj (app (atom "typeof") [b; c]) in
           let stmt = forall [("A", tm); ("B", tm); ("C", ty)]
             (arrow evalAB (arrow typeofAC typeofBC)) in
           let absR = app (atom "abs") [var ~tag:Eigen "R" 0] in
           let evalabsR = obj (app (atom "eval") [absR; absR]) in
           let arrowST = app (atom "arrow") [var ~tag:Eigen "S" 0;
                                             var ~tag:Eigen "T" 0] in
           let typeofabsR = obj (app (atom "typeof") [absR; arrowST]) in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply_forall stmt [evalabsR; typeofabsR])) ;

      "Unification failure during forall application" >::
        (fun () ->
           let h0 = parse ("forall (A : tm) (B : tm) (C : ty), " ^
                             "{eval A B} -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}" in
           let h2 = parse "{bad (abs R) (arrow S T)}" in
             assert_raises (Failure "Unification failure")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "Case application" >::
        (fun () ->
           (* eval (abs R) (abs R).
              eval (app M N) V :- eval M (abs R), eval (R N) V.

              case {eval A B} *)
           let str = "eval (abs R) (abs R).\n" ^
             "eval (app M N) V :- eval M (abs R), eval (R N) V." in
           let prog = Parser.clauses Lexer.token (Lexing.from_string str) in
           let a = var ~tag:Eigen "A" 0 in
           let b = var ~tag:Eigen "B" 0 in
           let term = obj (app (atom "eval") [a; b]) in
             match case term prog with
               | [(f1, []); (f2, [b1; b2])] ->
                   f1 () ;
                   assert_pprint_equal "{eval (abs R) (abs R)}" term ;
                   f2 () ;
                   assert_pprint_equal "{eval (app M N) V}" term ;
                   assert_pprint_equal "{eval M (abs R)}" b1 ;
                   assert_pprint_equal "{eval (R N) V}" b2 
               | _ -> assert_failure "Pattern mismatch") ;
      
      "Restricted case application" >::
        (fun () ->
           (* eval (abs R) (abs R).
              eval (app M N) V :- eval M (abs R), eval (R N) V.

              case {eval A B} which has inactive restriction 1 *)
           let str = "eval (abs R) (abs R).\n" ^
             "eval (app M N) V :- eval M (abs R), eval (R N) V." in
           let prog = Parser.clauses Lexer.token (Lexing.from_string str) in
           let a = var ~tag:Eigen "A" 0 in
           let b = var ~tag:Eigen "B" 0 in
           let term = inactive_obj (app (atom "eval") [a; b]) 1 in
             match case term prog with
               | [(f1, []); (f2, [b1; b2])] ->
                   f1 () ;
                   assert_pprint_equal "{eval (abs R) (abs R)}" term ;
                   f2 () ;
                   assert_pprint_equal "{eval (app M N) V}" term ;
                   assert_pprint_equal "{eval M (abs R)}*" b1 ;
                   assert_pprint_equal "{eval (R N) V}*" b2 
               | _ -> assert_failure "Pattern mismatch") ;
    ]
