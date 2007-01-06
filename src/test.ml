open OUnit

let tests = "LPP" >:::
  [
    Lppterm_test.tests ;
    Ndcore_test.tests ;
  ]
  
let _ = run_test_tt_main tests
