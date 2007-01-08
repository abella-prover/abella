open OUnit
open Lppterm
open Lppterm_lexer
open Lppterm_parser

let assert_pprint_equal = Lppterm_test.assert_pprint_equal

let parse str =
  lppterm token (Lexing.from_string str)

let tests =
  "LPPTerm Parser" >:::
    [
      "Simple object statement" >::
        (fun () ->
           let str = "{eval A B}" in
           let t = parse str in
             assert_pprint_equal str t) ;
      
      "Compound object statement" >::
        (fun () ->
           let str = "{eval (abs R) (abs R)}" in
           let t = parse str in
             assert_pprint_equal str t) ;
      
      "Implication object statement" >::
        (fun () ->
           let str = "{eval A B => typeof C D}" in
           let t = parse str in
             assert_pprint_equal str t) ;
      
      "Lambda object statement" >::
        (fun () ->
           let str = "{x1\\typeof x1 A}" in
           let t = parse str in
             assert_pprint_equal str t) ;
      
      "Pi lambda object statement" >::
        (fun () ->
           let str = "{pi x1\\typeof x1 A}" in
           let t = parse str in
             assert_pprint_equal str t) ;
      
      "Pi lambda implies object statement" >::
        (fun () ->
           let str = "{pi x1\\eval x1 A => typeof x1 B}" in
           let t = parse str in
             assert_pprint_equal str t) ;
    ]
