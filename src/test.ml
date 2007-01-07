open OUnit

let tests = "LPP" >:::
  [
    Norm_test.tests ;
    Unify_test.tests ;
  ]
  
let _ = run_test_tt_main tests
