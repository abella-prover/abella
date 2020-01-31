open OUnit
open Test_helper
open Typing

let assert_uterm_pprint_equal s t =
  assert_string_equal s (uterm_to_string t)

let assert_umetaterm_pprint_equal s t =
  assert_string_equal s (umetaterm_to_string t)

let assert_pprint_equal_parse str =
  assert_umetaterm_pprint_equal str (parse_umetaterm str)

let tests =
  "Parser" >:::
    [
      "Empty bodied clause" >::
        (fun () ->
           let str = "eval (abs R) (abs R)." in
             match parse_uclauses str with
               | [(None, t, [])] ->
                   assert_uterm_pprint_equal "eval (abs R) (abs R)" t
               | _ -> assert_failure "Pattern mismatch" ) ;

      "Typical clause" >::
        (fun () ->
           let str = "eval (app M N) V :- eval M (abs R), eval (R N) V." in
             match parse_uclauses str with
               | [(None, head, [b1; b2])] ->
                   assert_uterm_pprint_equal "eval (app M N) V" head ;
                   assert_uterm_pprint_equal "eval M (abs R)" b1 ;
                   assert_uterm_pprint_equal "eval (R N) V" b2 ;
               | _ -> assert_failure "Pattern mismatch" ) ;

      "Infix cons" >::
        (fun () ->
           assert_pprint_equal_parse "{member A (A :: B :: L)}") ;

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

      "Lambda cons" >::
        (fun () ->
           assert_pprint_equal_parse "x1\\a :: b") ;

      "Cons equality" >::
        (fun () ->
           assert_pprint_equal_parse "a :: b = a :: b") ;

      "Smaller restriction" >::
        (fun () ->
           assert_pprint_equal_parse "{A}*") ;

      "CoSmaller restriction" >::
        (fun () ->
           assert_pprint_equal_parse "foo +") ;

      "CoEqual restriction" >::
        (fun () ->
           assert_pprint_equal_parse "foo #") ;

      "Equal restriction" >::
        (fun () ->
           assert_pprint_equal_parse "{A}@") ;

      "Second smaller restriction" >::
        (fun () ->
           assert_pprint_equal_parse "{A}**") ;

      "Smaller restriction on predicate" >::
        (fun () ->
           assert_pprint_equal_parse "pred A B *") ;

      "Implies statement" >::
        (fun () ->
           assert_pprint_equal_parse "{A} -> {B}") ;

      "OR statement" >::
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B}") ;

      "AND statement" >::
        (fun () ->
           assert_pprint_equal_parse "{A} /\\ {B}") ;

      "AND within OR" >::
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B} /\\ {C}") ;

      "OR statement on right side of arrow" >::
        (fun () ->
           assert_pprint_equal_parse "{A} -> {B} \\/ {C}") ;

      "OR statement on left side of arrow" >::
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B} -> {C}") ;

      "Multiple OR statement" >::
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B} \\/ {C}") ;

      "Multiple OR statement (right assoc)" >::
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ ({B} \\/ {C})") ;

      "Arrow underneath OR" >::
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ ({B} -> {C})") ;

      "Forall" >::
        (fun () ->
           assert_pprint_equal_parse "forall A B, {C}") ;

      "Exists" >::
        (fun () ->
           assert_pprint_equal_parse "exists A B, {C}") ;

      "Exists on left of OR" >::
        (fun () ->
           assert_pprint_equal_parse "(exists A, {B}) \\/ {C}") ;

      "OR underneath exists" >::
        (fun () ->
           assert_pprint_equal_parse "exists A, {B} \\/ {C}") ;

      "Variable in context" >::
        (fun () ->
           assert_pprint_equal_parse "{L |- A}") ;

      "Simple predicate" >::
        (fun () ->
           assert_pprint_equal_parse "head A B") ;

      "Complex predicate" >::
        (fun () ->
           assert_pprint_equal_parse "head (hyp A) (conc B)") ;

    ]
