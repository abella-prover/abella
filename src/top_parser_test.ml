open OUnit
open Test_helper
open Lppterm
open Top_lexer
open Top_parser

let assert_pprint_equal_parse str =
  assert_pprint_equal str (parse_lppterm str)

let tests =
  "Top Parser" >:::
    [
      "Simple object statement" >::
        (fun () ->
           assert_pprint_equal_parse "{eval A B}") ;
      
      "Compound object statement" >::
        (fun () ->
           assert_pprint_equal_parse "{eval (abs R) (abs R)}") ;
      
      "Implication object statement" >::
        (fun () ->
           assert_pprint_equal_parse "{eval A B => typeof C D}") ;
      
      "Lambda object statement" >::
        (fun () ->
           assert_pprint_equal_parse "{x1\\typeof x1 A}") ;
      
      "Pi lambda object statement" >::
        (fun () ->
           assert_pprint_equal_parse "{pi x1\\typeof x1 A}") ;
      
      "Pi lambda implies object statement" >::
        (fun () ->
           assert_pprint_equal_parse "{pi x1\\eval x1 A => typeof x1 B}") ;
      
      "Active restriction" >::
        (fun () ->
           assert_pprint_equal_parse "{A}*") ;

      "Inactive restriction" >::
        (fun () ->
           assert_pprint_equal_parse "{A}@") ;

      "Implies statement" >::
        (fun () ->
           assert_pprint_equal_parse "{A} -> {B}") ;
      
      "OR statement" >::
        (fun () ->
           assert_pprint_equal_parse "{A} or {B}") ;
      
      "OR statement on right side of arrow" >::
        (fun () ->
           assert_pprint_equal_parse "{A} -> {B} or {C}") ;
      
      "OR statement on left side of arrow" >::
        (fun () ->
           assert_pprint_equal_parse "{A} or {B} -> {C}") ;

      "Multiple OR statement" >::
        (fun () ->
           assert_pprint_equal_parse "{A} or {B} or {C}") ;

      "Multiple OR statement (right assoc)" >::
        (fun () ->
           assert_pprint_equal_parse "{A} or ({B} or {C})") ;

      "Arrow underneath OR" >::
        (fun () ->
           assert_pprint_equal_parse "{A} or ({B} -> {C})") ;

    ]
