open OUnit
open Term
open Term.Notations
open Lppterm
  
let id x = x
  
let assert_pprint_equal s t =
  assert_equal ~printer:id s (lppterm_to_string t)

let a = var ~tag:Eigen "A" 0
let b = var ~tag:Eigen "B" 0
let c = var ~tag:Eigen "C" 0
    
let tests =
  "LPP Term" >:::
    [
      "Print object" >::
        (fun () ->
           let t = obj (app (const "eval") [a; b]) in
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
           let evalAB = obj (app (const "eval") [a; b]) in
           let t = forall ["A"] evalAB in
             assert_pprint_equal "forall A, {eval A B}" t) ;
      
      "Print active restricted object" >::
        (fun () ->
           let evalAB = active_obj (app (const "eval") [a; b]) 1 in
           let typeofAB = obj (app (const "typeof") [a; b]) in
           let t = arrow evalAB typeofAB in
             assert_pprint_equal "{eval A B}* -> {typeof A B}" t) ;
      
      "Print inactive restricted object" >::
        (fun () ->
           let evalAB = inactive_obj (app (const "eval") [a; b]) 1 in
           let typeofAB = obj (app (const "typeof") [a; b]) in
           let t = arrow evalAB typeofAB in
             assert_pprint_equal "{eval A B}@ -> {typeof A B}" t) ;
      
      "Print single element context" >::
        (fun () ->
           let evalAB = app (const "eval") [a; b] in
           let typeofAB = app (const "typeof") [a; b] in
           let t = context_obj [evalAB] typeofAB in
             assert_pprint_equal "{eval A B |- typeof A B}" t) ;
      
      "Print mutiple element context" >::
        (fun () ->
           let evalAB = app (const "eval") [a; b] in
           let evalAC = app (const "eval") [a; c] in
           let typeofAB = app (const "typeof") [a; b] in
           let t = context_obj [evalAB; evalAC] typeofAB in
             assert_pprint_equal "{eval A B, eval A C |- typeof A B}" t) ;
    ]
