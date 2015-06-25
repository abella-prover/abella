open OUnit
open Test_helper

let tests = "Abella" >:::
  [
    Unify_test.tests ;
    Term_test.tests ;
    Context_test.tests ;
    Graph_test.tests ;
    Subordination_test.tests ;
    Metaterm_test.tests ;
    Typing_test.tests ;
    Parser_test.tests ;
    Tactics_test.tests ;
    Prover_test.tests ;
  ]

let tests = extract_tests [] tests

let _ = run_test_tt_main tests
