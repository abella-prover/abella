open OUnit
open Lppterm
open Lexer
open Parser

let assert_pprint_equal = Lppterm_test.assert_pprint_equal

let parse_lppterm str =
  lppterm token (Lexing.from_string str)

let parse_clauses str =
  clauses token (Lexing.from_string str)

let tests =
  "Parser" >:::
    [
      "Simple object statement" >::
        (fun () ->
           let str = "{eval A B}" in
           let t = parse_lppterm str in
             assert_pprint_equal str t) ;
      
      "Compound object statement" >::
        (fun () ->
           let str = "{eval (abs R) (abs R)}" in
           let t = parse_lppterm str in
             assert_pprint_equal str t) ;
      
      "Implication object statement" >::
        (fun () ->
           let str = "{eval A B => typeof C D}" in
           let t = parse_lppterm str in
             assert_pprint_equal str t) ;
      
      "Lambda object statement" >::
        (fun () ->
           let str = "{x1\\typeof x1 A}" in
           let t = parse_lppterm str in
             assert_pprint_equal str t) ;
      
      "Pi lambda object statement" >::
        (fun () ->
           let str = "{pi x1\\typeof x1 A}" in
           let t = parse_lppterm str in
             assert_pprint_equal str t) ;
      
      "Pi lambda implies object statement" >::
        (fun () ->
           let str = "{pi x1\\eval x1 A => typeof x1 B}" in
           let t = parse_lppterm str in
             assert_pprint_equal str t) ;
      
      "Active restriction" >::
        (fun () ->
           let str = "{A}**" in
           let t = parse_lppterm str in
             assert_pprint_equal str t) ;

      "Inactive restriction" >::
        (fun () ->
           let str = "{A}@@" in
           let t = parse_lppterm str in
             assert_pprint_equal str t) ;
      
      "Empty bodied clause" >::
        (fun () ->
           let str = "eval (abs R) (abs R)." in
             match parse_clauses str with
               | [(t, [])] -> 
                   assert_pprint_equal "{eval (abs R) (abs R)}" t
               | _ -> assert_failure "Pattern mismatch" ) ;

      "Typical clause" >::
        (fun () ->
           let str = "eval (app M N) V :- eval M (abs R), eval (R N) V." in
             match parse_clauses str with
               | [(head, [b1; b2])] -> 
                   assert_pprint_equal "{eval (app M N) V}" head ;
                   assert_pprint_equal "{eval M (abs R)}" b1 ;
                   assert_pprint_equal "{eval (R N) V}" b2 ;
               | _ -> assert_failure "Pattern mismatch" ) ;
      
    ]
