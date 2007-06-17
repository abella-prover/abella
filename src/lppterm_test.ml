open OUnit
open Test_helper
open Term
open Term.Notations
open Lppterm
  
let var_a = var ~tag:Eigen "A" 0
let var_b = var ~tag:Eigen "B" 0
let var_c = var ~tag:Eigen "C" 0

let a = termobj var_a
let b = termobj var_b
let c = termobj var_c
    
let tests =
  "LPP Term" >:::
    [
      "Print object" >::
        (fun () ->
           let t = termobj (app (const "eval") [var_a; var_b]) in
             assert_pprint_equal "{eval A B}" t) ;
      
      "Print arrow" >::
        (fun () ->
           let t = arrow a b  in
             assert_pprint_equal "{A} -> {B}" t) ;
      
      "Print multiple arrows" >::
        (fun () ->
           let t = arrow a (arrow b c)  in
             assert_pprint_equal "{A} -> {B} -> {C}" t) ;
      
      "Print forall" >::
        (fun () ->
           let t = forall ["A"] b in
             assert_pprint_equal "forall A, {B}" t) ;
      
      "Print exists" >::
        (fun () ->
           let t = exists ["A"] b in
             assert_pprint_equal "exists A, {B}" t) ;
      
      "Print smaller restricted object" >::
        (fun () ->
           let t = apply_restriction Smaller a in
             assert_pprint_equal "{A}*" t) ;
      
      "Print equal restricted object" >::
        (fun () ->
           let t = apply_restriction Equal a in
             assert_pprint_equal "{A}@" t) ;

      "Print OR" >::
        (fun () ->
           let t = lpp_or a b in
             assert_pprint_equal "{A} or {B}" t) ;
           
      "Print multiple OR" >::
        (fun () ->
           let t = lpp_or (lpp_or a b) c in
             assert_pprint_equal "{A} or {B} or {C}" t) ;
           
      "Print multiple OR (right assoc)" >::
        (fun () ->
           let t = lpp_or a (lpp_or b c) in
             assert_pprint_equal "{A} or ({B} or {C})" t) ;
           
      "Print OR within arrow" >::
        (fun () ->
           let t = arrow a (lpp_or b c) in
             assert_pprint_equal "{A} -> {B} or {C}" t) ;
           
      "Print arrow within OR" >::
        (fun () ->
           let t = lpp_or (arrow a b) c in
             assert_pprint_equal "({A} -> {B}) or {C}" t) ;

      "Print exists left of OR" >::
        (fun () ->
           let t = lpp_or (exists ["A"] b) c in
             assert_pprint_equal "(exists A, {B}) or {C}" t) ;

      "Replace should descend underneath exists" >::
        (fun () ->
           let t = exists ["A"] b in
           let t' = replace_lppterm_vars [("B", var_c)] t in
             assert_pprint_equal "exists A, {C}" t') ;

      "Replace should not descend underneath exists if names are equal" >::
        (fun () ->
           let t = exists ["A"] a in
           let t' = replace_lppterm_vars [("A", var_b)] t in
             assert_pprint_equal "exists A, {A}" t') ;

      "Print non-empty context" >::
        (fun () ->
           let ctx = Context.add (const "L") Context.empty in
           let t = Obj(context_obj ctx var_a, Irrelevant) in
             assert_pprint_equal "{L |- A}" t) ;

    ]
