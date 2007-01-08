open OUnit

let tests = "LPP" >:::
  [
    Norm_test.tests ;
    Unify_test.tests ;
    Pprint_test.tests ;
    Lppterm_test.tests ;
    Lppterm_parser_test.tests ;
    Prover_test.tests ;
  ]
  
let _ = run_test_tt_main tests
