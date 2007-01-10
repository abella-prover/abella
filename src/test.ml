open OUnit

let tests = "LPP" >:::
  [
    Norm_test.tests ;
    Unify_test.tests ;
    Pprint_test.tests ;
    Lppterm_test.tests ;
    Parser_test.tests ;
    Top_parser_test.tests ;
    Tactics_test.tests ;
    Prover_test.tests ;
  ]
  
let _ = run_test_tt_main tests
