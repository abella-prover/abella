open OUnit
open Term
open Lppterm
  
let id x = x
  
let assert_pprint_equal s t =
  assert_equal ~printer:id s (lppterm_to_string t)
  
let tests =
  "LPP Term" >:::
    [
      "{eval P V}" >::
        (fun () ->
           let p = var "P" 0 in
           let v = var "V" 0 in
           let t = Obj(app (atom "eval") [p; v]) in
             assert_pprint_equal "{eval P V}" t) ;
      
      "{A} -> {B}" >::
        (fun () ->
           let a = var "A" 0 in
           let b = var "B" 0 in
           let t = Arrow(Obj(a), Obj(b))  in
             assert_pprint_equal "{A} -> {B}" t) ;
      
      "{A} -> {B} -> {C}" >::
        (fun () ->
           let a = var "A" 0 in
           let b = var "B" 0 in
           let c = var "C" 0 in
           let t = Arrow(Arrow(Obj(a), Obj(b)), Obj(c))  in
             assert_pprint_equal "{A} -> {B} -> {C}" t) ;
      
      "forall (A : tm), {eval A}" >::
        (fun () ->
           let a = var "A" 0 in
           let evalA = Obj(app (atom "eval") [a]) in
           let tm = atom "tm" in
           let t = Forall([(a, tm)], evalA) in
             assert_pprint_equal "forall (A : tm), {eval A}" t) ;
    ]
