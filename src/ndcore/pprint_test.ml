open OUnit
open Term
open Term.Notations
open Pprint

let id x = x

let assert_pprint_equal s t = assert_equal ~printer:id s (term_to_string t)

let tests =
  "Pprint" >:::
    [
      "eval P V" >::
        (fun () ->
           let p = var "P" 0 in
           let v = var "V" 0 in
           let t = app (atom "eval") [p; v] in
             assert_pprint_equal "eval P V" t) ;

      "eval (abs R) (abs R)" >::
        (fun () ->
           let absR = (app (atom "abs") [var "R" 0]) in
           let t = app (atom "eval") [absR; absR] in
             assert_pprint_equal "eval (abs R) (abs R)" t) ;
      
      "A => B" >::
        (fun () ->
           set_infix [("=>", Right)] ;
           let a = var "A" 0 in
           let b = var "B" 0 in
           let t = app (atom "=>") [a; b] in
             assert_pprint_equal "A => B" t) ;

      "pi x\\eq x x" >::
        (fun () ->
           let t = app (atom "pi") [1 // (app (atom "eq") [db 1; db 1])] in
             assert_pprint_equal "pi x1\\eq x1 x1" t) ;

      "pi x\\typeof x U => typeof (R x) T" >::
        (fun () ->
           set_infix [("=>", Right)] ;
           let typeofxU = app (atom "typeof") [db 1; var "U" 0] in
           let rx = app (var "R" 0) [db 1] in
           let typeofRxT = app (atom "typeof") [rx; var "T" 0] in
           let t = app (atom "pi")
             [1 // (app (atom "=>") [typeofxU; typeofRxT])] in
             assert_pprint_equal "pi x1\\typeof x1 U => typeof (R x1) T" t) ;
    ]
    
