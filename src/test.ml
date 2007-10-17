open OUnit

let tests = "LPP" >:::
  [
    Term_test.tests ;
    Unify_test.tests ;
    Metaterm_test.tests ;
    Parser_test.tests ;
    Tactics_test.tests ;
    Prover_test.tests ;
    Context_test.tests ;
  ]
  
let _ = run_test_tt_main tests
