open OUnit
open Test_helper
open Term
open Subordination

let tm = tybase (atybase "tm")
let tp = tybase (atybase "tp")
let t_lam = tyarrow [tp; tyarrow [tm] tm] tm

let tests =
  "Subordination" >::: [
    "STLC example" >::
      (fun () ->
         let sr = update empty t_lam in
         let sr = close sr [atybase "tm"; atybase "tp"] in
           assert_true (query sr tp tp) ;
           assert_true (query sr tm tm) ;
           assert_true (query sr tp tm) ;
           assert_false (query sr tm tp) ;
      );

    "Subordination should only hold for closed types" >::
      (fun () ->
         let sr = update empty t_lam in
           assert_true (query sr tp tp) ;
           assert_true (query sr tm tm) ;
           assert_true (query sr tp tm) ;
           assert_true (query sr tm tp) ;
      );

    "Closed should check predecessors" >::
      (fun () ->
         let sr = update empty t_lam in
           assert_raises
             (Failure "Cannot close tm without closing tp")
             (fun () -> close sr [atybase "tm"])
      );

    "Should not be able to subordinate closed types" >::
      (fun () ->
         let sr = close empty [atybase "tm"] in
           assert_raises
             (Failure "Type tm is closed and cannot be subordinated by tp")
             (fun () -> update sr t_lam)
      );

    "Should be able to properly update closed types" >::
      (fun () ->
         let sr = update empty t_lam in
         let sr = close sr [atybase "tm"; atybase "tp"] in
           ignore (update sr t_lam)
      );

    "Should be able to sequentially close" >::
      (fun () ->
         let sr = update empty t_lam in
         let sr = close sr [atybase "tp"] in
           ignore (close sr [atybase "tm"])
      );

    "Subordination should by transitive" >::
      (fun () ->
         let a = tybase (atybase "a") in
         let b = tybase (atybase "b") in
         let c = tybase (atybase "c") in
         let sr = update empty (tyarrow [tyarrow [a] b] c) in
         let sr = close sr [atybase "a"; atybase "b"; atybase "c"] in
           assert_true (query sr a b) ;
           assert_true (query sr b c) ;
           assert_true (query sr a c) ;
      );

(* [obsolete as of a7df40b7e45b845c3639bc28367ee50d81cf967a]
    "Ensure should error on implicit subordination" >::
      (fun () ->
         let sr = update empty t_lam in
           assert_raises
             (Failure "Type tm cannot be made subordinate to tp without explicit declaration")
             (fun () -> ensure sr (tyarrow [tm] tp))
      );
*)

  ]
