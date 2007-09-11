open OUnit
open Test_helper
open Term
open Term.Notations
open Lppterm
  
let var_a = var Eigen "A" 0
let var_b = var Eigen "B" 0
let var_c = var Eigen "C" 0

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
           let t = apply_restriction (Smaller 1) a in
             assert_pprint_equal "{A}*" t) ;
      
      "Print equal restricted object" >::
        (fun () ->
           let t = apply_restriction (Equal 1) a in
             assert_pprint_equal "{A}@" t) ;

      "Print second smaller restricted object" >::
        (fun () ->
           let t = apply_restriction (Smaller 2) a in
             assert_pprint_equal "{A}**" t) ;
      
      "Print OR" >::
        (fun () ->
           let t = lpp_or a b in
             assert_pprint_equal "{A} \\/ {B}" t) ;
           
      "Print AND" >::
        (fun () ->
           let t = lpp_and a b in
             assert_pprint_equal "{A} /\\ {B}" t) ;
           
      "Print multiple \\/" >::
        (fun () ->
           let t = lpp_or (lpp_or a b) c in
             assert_pprint_equal "{A} \\/ {B} \\/ {C}" t) ;
           
      "Print multiple OR (right assoc)" >::
        (fun () ->
           let t = lpp_or a (lpp_or b c) in
             assert_pprint_equal "{A} \\/ ({B} \\/ {C})" t) ;
           
      "Print OR within arrow" >::
        (fun () ->
           let t = arrow a (lpp_or b c) in
             assert_pprint_equal "{A} -> {B} \\/ {C}" t) ;

      "Print arrow within OR" >::
        (fun () ->
           let t = lpp_or (arrow a b) c in
             assert_pprint_equal "({A} -> {B}) \\/ {C}" t) ;

      "Print OR within AND" >::
        (fun () ->
           let t = lpp_and a (lpp_or b c) in
             assert_pprint_equal "{A} /\\ ({B} \\/ {C})" t) ;

      "Print AND within OR" >::
        (fun () ->
           let t = lpp_or a (lpp_and b c) in
             assert_pprint_equal "{A} \\/ {B} /\\ {C}" t) ;

      "Print exists left of OR" >::
        (fun () ->
           let t = lpp_or (exists ["A"] b) c in
             assert_pprint_equal "(exists A, {B}) \\/ {C}" t) ;

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

      "Replace should not capture exists variables" >::
        (fun () ->
           let t = exists ["A"] b in
           let t' = replace_lppterm_vars [("B", var_a)] t in
             assert_pprint_equal "exists A0, {A}" t') ;
      
      "Print non-empty context" >::
        (fun () ->
           let ctx = Context.add (const "L") Context.empty in
           let t = Obj(context_obj ctx var_a, Irrelevant) in
             assert_pprint_equal "{L |- A}" t) ;

      "Print predicate" >::
        (fun () ->
           let p = app (const "head") [const "A"; const "B"] in
           let t = Pred(p, Irrelevant) in
             assert_pprint_equal "head A B" t) ;

      "Print restricted predicate" >::
        (fun () ->
           let p = app (const "head") [const "A"; const "B"] in
           let t = Pred(p, Smaller 1) in
             assert_pprint_equal "head A B *" t) ;
      
      "Print equality" >::
        (fun () ->
           let t = termobj (app (const "=") [const "A"; const "B"]) in
             assert_pprint_equal "{A = B}" t) ;

      "Print object quantifier inside of predicate" >::
        (fun () ->
           let t = pred (app (const "prove")
                           [app (const "pi") [const "G"]]) in
             assert_pprint_equal "prove (pi G)" t) ;

      "Normalize should move all implications to the context" >::
        (fun () ->
           let ctx = Context.add (const "L") Context.empty in
           let bc = app (const "=>") [const "B"; const "C"] in
           let abc = app (const "=>") [const "A"; bc] in
           let t = Obj(context_obj ctx abc, Irrelevant) in
             assert_pprint_equal "{L |- A => B => C}" t ;
             assert_pprint_equal "{L, A, B |- C}" (normalize t)) ;

      "Normalize should instantiate pi x\\ with nominal constant" >::
        (fun () ->
           let t = app (const "pi") [1 // app (const "pred") [db 1; db 1]] in
           let t = termobj t in
             assert_pprint_equal "{pi x1\\pred x1 x1}" t ;
             assert_pprint_equal "{pred n1 n1}" (normalize t)) ;

      "Normalize should rename bound variables if needed" >::
        (fun () ->
           let const_a = const "A" in
           let p = const "p" in
           let t = forall ["A"]
             (arrow (pred (app p [var_a])) (pred (app p [const_a])))
           in
             assert_pprint_equal "forall A0, p A -> p A0" (normalize t)) ;

      "Normalize should rename nested binders" >::
        (fun () ->
           (* The var_a should force renaming of the A which should
              cascade and force renaming of A0 *)
           let eq = pred (app (const "=") [const "A"; const "A0"]) in
           let t = Binding(Forall, ["A"],
                           Arrow(pred var_a, Binding(Forall, ["A0"], eq)))
           in
             assert_pprint_equal "forall A0, A -> (forall A1, A0 = A1)"
               (normalize t) );

      "Abstract should replace eigen variables with lambda abstractions" >::
        (fun () ->
           let t = app (const "foo") [var_a; var_b] in
             assert_term_pprint_equal "x1\\x2\\foo x1 x2" (abstract_eigen t))

    ]
