open OUnit
open Test_helper

let tests = "Abella" >:::
  [
    (*TODO Test_unify.tests ;*)
    Test_term.tests ;
    Test_context.tests ;
    Test_graph.tests ;
    Test_subordination.tests ;
    Test_metaterm.tests ;
    (*TODO Test_typing.tests ;*)
    (*TODO Test_parser.tests ;*)
    (*TODO Test_tactics.tests ;*)
    (*TODO Test_prover.tests ;*)
  ]

let tests = extract_tests [] tests

let _ = run_test_tt_main tests
