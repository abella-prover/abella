open Test_helper
open Abella_lib
open Term
open Subordination

let tm = tybase (atybase "tm")
let tp = tybase (atybase "tp")
let t_lam = tyarrow [tp; tyarrow [tm] tm] tm

let tests =
  suite "Subordination" [
    test_case "STLC example"
      (fun () ->
         let sr = update empty t_lam in
         let sr = close sr [atybase "tm"; atybase "tp"] in
           Alcotest.check Alcotest.bool "expected true" true (query sr tp tp) ;
           Alcotest.check Alcotest.bool "expected true" true (query sr tm tm) ;
           Alcotest.check Alcotest.bool "expected true" true (query sr tp tm) ;
           Alcotest.check Alcotest.bool "expected false" false (query sr tm tp) ;
      );

    test_case "Subordination should only hold for closed types"
      (fun () ->
         let sr = update empty t_lam in
           Alcotest.check Alcotest.bool "expected true" true (query sr tp tp) ;
           Alcotest.check Alcotest.bool "expected true" true (query sr tm tm) ;
           Alcotest.check Alcotest.bool "expected true" true (query sr tp tm) ;
           Alcotest.check Alcotest.bool "expected true" true (query sr tm tp) ;
      );

    test_case "Closed should check predecessors"
      (fun () ->
         let sr = update empty t_lam in
           Alcotest.check_raises
             "Cannot close tm without closing tp"
             (Failure "Cannot close tm without closing tp")
             (fun () -> ignore (close sr [atybase "tm"]))
      );

    test_case "Should not be able to subordinate closed types"
      (fun () ->
         let sr = close empty [atybase "tm"] in
           Alcotest.check_raises
             "Type tm is closed and cannot be subordinated by tp"
             (Failure "Type tm is closed and cannot be subordinated by tp")
             (fun () -> ignore (update sr t_lam))
      );

    test_case "Should be able to properly update closed types"
      (fun () ->
         let sr = update empty t_lam in
         let sr = close sr [atybase "tm"; atybase "tp"] in
           ignore (update sr t_lam)
      );

    test_case "Should be able to sequentially close"
      (fun () ->
         let sr = update empty t_lam in
         let sr = close sr [atybase "tp"] in
           ignore (close sr [atybase "tm"])
      );

    test_case "Subordination should by transitive"
      (fun () ->
         let a = tybase (atybase "a") in
         let b = tybase (atybase "b") in
         let c = tybase (atybase "c") in
         let sr = update empty (tyarrow [tyarrow [a] b] c) in
         let sr = close sr [atybase "a"; atybase "b"; atybase "c"] in
           Alcotest.check Alcotest.bool "expected true" true (query sr a b) ;
           Alcotest.check Alcotest.bool "expected true" true (query sr b c) ;
           Alcotest.check Alcotest.bool "expected true" true (query sr a c) ;
      );

(* [obsolete as of a7df40b7e45b845c3639bc28367ee50d81cf967a]
    test_case "Ensure should error on implicit subordination"
      (fun () ->
         let sr = update empty t_lam in
           Alcotest.check_raises
             "Type tm cannot be made subordinate to tp \
              without explicit declaration"
             (Failure
                "Type tm cannot be made subordinate to tp \
                 without explicit declaration")
             (fun () -> ignore (ensure sr (tyarrow [tm] tp)))
      );
*)

  ]
