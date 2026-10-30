open Test_helper
open Abella_lib
open Typing

let assert_uterm_pprint_equal s t =
  Alcotest.check Alcotest.string "strings differ" s (uterm_to_string t)

let assert_umetaterm_pprint_equal s t =
  Alcotest.check Alcotest.string "strings differ" s (umetaterm_to_string t)

let assert_pprint_equal_parse str =
  assert_umetaterm_pprint_equal str (parse_umetaterm str)

let tests =
  suite "Parser" [
      test_case "Empty bodied clause"
        (fun () ->
           let str = "eval (abs R) (abs R)." in
             match parse_uclauses str with
               | [{ el = (None, t, []) ; _ }] ->
                   assert_uterm_pprint_equal "eval (abs R) (abs R)" t
               | _ -> Alcotest.fail "Pattern mismatch" ) ;

      test_case "Typical clause"
        (fun () ->
           let str = "eval (app M N) V :- eval M (abs R), eval (R N) V." in
             match parse_uclauses str with
               | [{ el = (None, head, [b1; b2]) ; _ }] ->
                   assert_uterm_pprint_equal "eval (app M N) V" head ;
                   assert_uterm_pprint_equal "eval M (abs R)" b1 ;
                   assert_uterm_pprint_equal "eval (R N) V" b2 ;
               | _ -> Alcotest.fail "Pattern mismatch" ) ;

      test_case "Infix cons"
        (fun () ->
           assert_pprint_equal_parse "{member A (A :: B :: L)}") ;

      test_case "Simple object statement"
        (fun () ->
           assert_pprint_equal_parse "{eval A B}") ;

      test_case "Compound object statement"
        (fun () ->
           assert_pprint_equal_parse "{eval (abs R) (abs R)}") ;

      test_case "Implication object statement"
        (fun () ->
           assert_pprint_equal_parse "{eval A B => typeof C D}") ;

      test_case "Lambda object statement"
        (fun () ->
           assert_pprint_equal_parse "{x1\\typeof x1 A}") ;

      test_case "Pi lambda object statement"
        (fun () ->
           assert_pprint_equal_parse "{pi x1\\typeof x1 A}") ;

      test_case "Pi lambda implies object statement"
        (fun () ->
           assert_pprint_equal_parse "{pi x1\\eval x1 A => typeof x1 B}") ;

      test_case "Lambda cons"
        (fun () ->
           assert_pprint_equal_parse "x1\\a :: b") ;

      test_case "Cons equality"
        (fun () ->
           assert_pprint_equal_parse "a :: b = a :: b") ;

      test_case "Smaller restriction"
        (fun () ->
           assert_pprint_equal_parse "{A}*") ;

      test_case "CoSmaller restriction"
        (fun () ->
           assert_pprint_equal_parse "foo +") ;

      test_case "CoEqual restriction"
        (fun () ->
           assert_pprint_equal_parse "foo #") ;

      test_case "Equal restriction"
        (fun () ->
           assert_pprint_equal_parse "{A}@") ;

      test_case "Second smaller restriction"
        (fun () ->
           assert_pprint_equal_parse "{A}**") ;

      test_case "Smaller restriction on predicate"
        (fun () ->
           assert_pprint_equal_parse "pred A B *") ;

      test_case "Implies statement"
        (fun () ->
           assert_pprint_equal_parse "{A} -> {B}") ;

      test_case "OR statement"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B}") ;

      test_case "AND statement"
        (fun () ->
           assert_pprint_equal_parse "{A} /\\ {B}") ;

      test_case "AND within OR"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B} /\\ {C}") ;

      test_case "OR statement on right side of arrow"
        (fun () ->
           assert_pprint_equal_parse "{A} -> {B} \\/ {C}") ;

      test_case "OR statement on left side of arrow"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B} -> {C}") ;

      test_case "Multiple OR statement"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ {B} \\/ {C}") ;

      test_case "Multiple OR statement (right assoc)"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ ({B} \\/ {C})") ;

      test_case "Arrow underneath OR"
        (fun () ->
           assert_pprint_equal_parse "{A} \\/ ({B} -> {C})") ;

      test_case "Forall"
        (fun () ->
           assert_pprint_equal_parse "forall A B, {C}") ;

      test_case "Exists"
        (fun () ->
           assert_pprint_equal_parse "exists A B, {C}") ;

      test_case "Exists on left of OR"
        (fun () ->
           assert_pprint_equal_parse "(exists A, {B}) \\/ {C}") ;

      test_case "OR underneath exists"
        (fun () ->
           assert_pprint_equal_parse "exists A, {B} \\/ {C}") ;

      test_case "Variable in context"
        (fun () ->
           assert_pprint_equal_parse "{L |- A}") ;

      test_case "Simple predicate"
        (fun () ->
           assert_pprint_equal_parse "head A B") ;

      test_case "Complex predicate"
        (fun () ->
           assert_pprint_equal_parse "head (hyp A) (conc B)") ;

    ]
