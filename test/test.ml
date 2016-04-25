open OUnit
open Test_helper

let tests = "Abella" >:::
  [
    (*Test_unify.tests ; other compiler errors *)
    (*Test_term.tests ; Parser must define term as %start *)
    Test_context.tests ;
    Test_graph.tests ;
    Test_subordination.tests ;
    (*Test_metaterm.tests ; Parser must define metaterm as %start *)
    (*Test_typing.tests ; other compiler errors *)
    (*Test_parser.tests ; other compiler errors *)
    (*Test_tactics.tests ; other compiler errors *)
    (*Test_prover.tests ; other compiler errors *)
  ]

let tests = extract_tests [] tests

let _ = run_test_tt_main tests
