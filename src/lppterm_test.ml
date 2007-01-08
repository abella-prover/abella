open OUnit
open Term
open Term.Notations
open Lppterm
  
let id x = x
  
let assert_pprint_equal s t =
  assert_equal ~printer:id s (lppterm_to_string t)

(* TODO - change these to eigen vars? *)
let a = var "A" 0
let b = var "B" 0
let c = var "C" 0
    
let tests =
  "LPP Term" >:::
    [
      "Print object" >::
        (fun () ->
           let t = obj (app (atom "eval") [a; b]) in
             assert_pprint_equal "{eval A B}" t) ;
      
      "Print arrow" >::
        (fun () ->
           let t = arrow (obj a) (obj b)  in
             assert_pprint_equal "{A} -> {B}" t) ;
      
      "Print multiple arrows" >::
        (fun () ->
           let t = arrow (arrow (obj a) (obj b)) (obj c)  in
             assert_pprint_equal "{A} -> {B} -> {C}" t) ;
      
      "Print forall" >::
        (fun () ->
           let evalAB = obj (app (atom "eval") [a; b]) in
           let tm = atom "tm" in
           let t = forall [(a, tm)] evalAB in
             assert_pprint_equal "forall (A : tm), {eval A B}" t) ;
      
      "Print active restricted object" >::
        (fun () ->
           let evalAB = active_obj (app (atom "eval") [a; b]) 1 in
           let typeofAB = obj (app (atom "typeof") [a; b]) in
           let t = arrow evalAB typeofAB in
             assert_pprint_equal "{eval A B}* -> {typeof A B}" t) ;
      
      "Print inactive restricted object" >::
        (fun () ->
           let evalAB = inactive_obj (app (atom "eval") [a; b]) 1 in
           let typeofAB = obj (app (atom "typeof") [a; b]) in
           let t = arrow evalAB typeofAB in
             assert_pprint_equal "{eval A B} -> {typeof A B}" t) ;
      
      "Simple object cut" >::
        (fun () ->
           let atob = obj (app (atom "=>") [a; b]) in
           let t = object_cut atob (obj a) in
             assert_pprint_equal "{B}" t) ;
      
      "Compound object cut" >::
        (fun () ->
           let evalAB = app (atom "eval") [a; b] in
           let typeofBC = app (atom "typeof") [b; c] in
           let imp = obj (app (atom "=>") [evalAB; typeofBC]) in
           let t = object_cut imp (obj evalAB) in
             assert_pprint_equal "{typeof B C}" t) ;

      "Simple object instantiation" >::
        (fun () ->
           (* (pi x\ eval x B) instantiated with A *)
           let evalxB = app (atom "eval") [db 1; b] in
           let pi_evalxB = obj (app (atom "pi") [1 // evalxB]) in
           let t = object_inst pi_evalxB a in
             assert_pprint_equal "{eval A B}" t) ;

      "Forall application" >::
        (fun () ->
           (* forall (A : tm) (B : tm) (C : ty),
                {eval A B} -> {typeof A C} -> {typeof B C}
              instantiated with {eval (abs R) (abs R)}
                                {typeof (abs R) (arrow S T)} *)
           let tm = atom "tm" in
           let ty = atom "ty" in
           let evalAB = obj (app (atom "eval") [a; b]) in
           let typeofAC = obj (app (atom "typeof") [a; c]) in
           let typeofBC = obj (app (atom "typeof") [b; c]) in
             (* TODO - these should not be these kind of variables? *)
           let stmt = forall [(a, tm); (b, tm); (c, ty)]
             (arrow evalAB (arrow typeofAC typeofBC)) in
           let absR = app (atom "abs") [var ~tag:Eigen "R" 0] in
           let evalabsR = obj (app (atom "eval") [absR; absR]) in
           let arrowST = app (atom "arrow") [var ~tag:Eigen "S" 0;
                                             var ~tag:Eigen "T" 0] in
           let typeofabsR = obj (app (atom "typeof") [absR; arrowST]) in
           let t = apply_forall stmt [evalabsR; typeofabsR] in
             assert_pprint_equal "{eval (abs R) (arrow S T)}" t) ;

(* TODO - will this mess up the logic vars and if so how do we reset *)
    ]
