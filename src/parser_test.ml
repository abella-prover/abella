open OUnit
open Test_helper
open Lppterm
open Lexer
open Parser

let parse_clauses str =
  clauses token (Lexing.from_string str)

let tests =
  "Parser" >:::
    [
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
