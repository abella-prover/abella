open OUnit
open Term
open Term.Notations
open Unify
open Test_helper

let right_unify ?(used=[]) t1 t2 =
  assert_ty_equal (tc [] t1) (tc [] t2) ;
  right_unify ~used t1 t2

let left_unify ?(used=[]) t1 t2 =
  assert_ty_equal (tc [] t1) (tc [] t2) ;
  left_unify ~used t1 t2

(* Extracting a variable at some position in a term,
 * used when we know a variable should be there, but don't know what it is
 * since it's fresh. *)
type path = L | A | H
let rec extract path t =
  match path, observe (hnorm t) with
    | L::tl, Lam(_,t) -> extract tl t
    | A::tl, App(_,t::_) -> extract tl t
    | H::_, App(t,_) -> observe t
    | _ -> assert false

let assert_raises_occurs_check f =
  try
    f () ;
    assert_failure "Expected OccursCheck"
  with
    | UnifyFailure OccursCheck -> ()

let assert_raises_unify_failure f =
  try
    f () ;
    assert_failure "Expected UnifyFailure"
  with
    | UnifyFailure _ -> ()

(* Tests from Nadathur's SML implementation *)
let tests =
  "Unify" >:::
    [
      (* Example 1, simple test involving abstractions *)
      "[x\\ x = x\\ M x]" >::
        (fun () ->
           let t1 = [("x",ity)] // db 1 in
           let m = var Logic "m" 1 iity in
           let t2 = [("x",ity)] // ( m ^^ [ db 1 ] ) in
             right_unify t1 t2 ;
             assert_term_equal ([("x",ity)] // db 1) m) ;

      (* Example 2, adds descending into constructors *)
      "[x\\ c x = x\\ c (N x)]" >::
        (fun () ->
           let n = var Logic "n" 1 iity in
           let c = const ~ts:1 "c" iity in
           let t1 = [("x",ity)] // (c ^^ [ db 1 ]) in
           let t2 = [("x",ity)] // (c ^^ [ n ^^ [ db 1 ] ]) in
             right_unify t1 t2 ;
             assert_term_equal ([("x",ity)] // db 1) n) ;

      (* Example 3, needs eta expanding on the fly *)
      "[x\\y\\ c y x = N]" >::
        (fun () ->
           let n = var Logic "n" 1 iiity in
           let c = const ~ts:1 "c" iiity in
           let t = [("y",ity); ("x",ity)] // (c ^^ [ db 1 ; db 2 ]) in
             right_unify t n ;
             assert_term_equal ([("y",ity); ("x",ity)] // (c ^^ [ db 1 ; db 2 ])) n) ;


      (* Example 4, on-the-fly eta, constructors at top-level *)
      "[x\\y\\ c x y = x\\ c (N x)]" >::
        (fun () ->
           let n = var Logic "n" 1 iity in
           let c = const ~ts:1 "c" iiity in
             right_unify
               ([("y",ity); ("x",ity)] // (c ^^ [db 2;db 1]))
               ([("x",ity)] // (c ^^ [n ^^ [db 1]])) ;
             assert_term_equal ([("x",ity)] // db 1) n) ;


      (* Example 5, flex-flex case where we need to raise & prune *)
      "[X1 a2 b3 = Y2 b3 c3]" >::
        (fun () ->
           let x = var Logic "x" 1 (tyarrow [aty; bty] ity) in
           let y = var Logic "y" 2 (tyarrow [bty; cty] ity) in
           let a = const ~ts:2 "a" aty in
           let b = const ~ts:3 "b" bty in
           let c = const ~ts:3 "c" cty in
           let t1 = x ^^ [ a ; b ] in
           let t2 = y ^^ [ b ; c ] in
             right_unify t1 t2 ;
             let h =
               match extract [L;H] x with
                 | Var {name=h;ts=1;tag=Logic;ty=ty} -> var Logic h 1 ty
                 | _ -> assert_failure "X should match x\\y\\ H ..."
             in
               assert_term_equal ([("a",aty); ("b",bty)] // (h ^^ [ db 2 ; db 1 ])) x ;
               assert_term_equal ([("b",bty); ("c",cty)] // (h ^^ [ a ; db 2 ])) y) ;

      (* Example 6, flex-rigid case involving raise & prune relative to an
       * embedded flex term. *)
      "[X1 a2 b3 = c1 (Y2 b3 d3)]" >::
        (fun () ->
           let x = var Logic "x" 1 iiity in
           let y = var Logic "y" 2 iiity in
           let a = const ~ts:2 "a" ity in
           let b = const ~ts:3 "b" ity in
           let c = const ~ts:1 "c" iity in
           let d3 = const ~ts:3 "d" ity in
             right_unify (x ^^ [a;b]) (c ^^ [y ^^ [b;d3]]) ;
             let h =
               match extract [L;A;H] x with
                 | Var {name=h;ts=1;tag=Logic;ty=ty} -> var Logic h 1 ty
                 | _ -> assert_failure "X should match x\\y\\ _ H .."
             in
               assert_term_equal ([("y",ity); ("x",ity)] // (c ^^ [h^^[db 2;db 1]])) x ;
               assert_term_equal ([("y",ity); ("x",ity)] // (h ^^ [a;db 2])) y) ;

      (* Example 7, multiple occurences *)
      "[e0 (X1 a2 b3) (X1 b3 d2) = e0 (Y2 b3 c3) (e0 b3 d2)]" >::
        (fun () ->
           let x = var Logic "x" 1 iiity in
           let y = var Logic "y" 2 iiity in
           let a = const ~ts:2 "a" ity in
           let b = const ~ts:3 "b" ity in
           let c = const ~ts:3 "c" ity in
           let d = const ~ts:2 "d" ity in
           let e = const ~ts:0 "e" iiity in
             right_unify
               (e ^^ [ x ^^ [a;b] ; x ^^ [b;d] ])
               (e ^^ [ y ^^ [b;c] ; e ^^ [b;d] ]) ;
             assert_term_equal ([("y",ity); ("x",ity)] // (e ^^ [db 2; db 1])) x ;
             assert_term_equal ([("y",ity); ("x",ity)] // (e ^^ [a; db 2])) y) ;

      (* Example 8, multiple occurences with a bound var as the rigid part
       * instead of a constant *)
      "[x\\ e0 (X1 a2 b3) (X x d2) = x\\ e0 (Y2 b3 c3) (e0 x d2)]" >::
        (fun () ->
           let x = var Logic "x" 1 iiity in
           let y = var Logic "y" 2 iiity in
           let a = const ~ts:2 "a" ity in
           let b = const ~ts:3 "b" ity in
           let d = const ~ts:2 "d" ity in
           let c = const ~ts:3 "c" ity in
           let e = const ~ts:0 "e" iiity in
             right_unify
               ([("x",ity)] // (e ^^ [ x ^^ [a;b] ; x ^^ [db 1;d]]))
               ([("x",ity)] // (e ^^ [ y ^^ [b;c] ; e ^^ [db 1;d] ])) ;
             assert_term_equal ([("y",ity); ("x",ity)] // (e ^^ [db 2;db 1])) x ;
             assert_term_equal ([("y",ity); ("x",ity)] // (e ^^ [a;db 2])) y) ;

      (* Example 9, flex-flex with same var at both heads *)
      "[X1 a2 b3 c3 = X1 c3 b3 a2]" >::
        (fun () ->
           let x = var Logic "x" 1 (tyarrow [aty; bty; aty] ity) in
           let a = const ~ts:2 "a" aty in
           let b = const ~ts:3 "b" bty in
           let c = const ~ts:3 "c" aty in
             right_unify (x ^^ [a;b;c]) (x ^^ [c;b;a]) ;
             let h =
               match extract [L;H] x with
                 | Var {name=h;ts=1;tag=Logic;ty=ty} -> var Logic h 1 ty
                 | _ -> assert_failure "X should match x\\y\\z\\ H ..."
             in
               assert_term_equal ([("a",aty); ("a",bty); ("c",aty)] // (h^^[db 2])) x) ;

      (* Example 10, failure due to OccursCheck *)
      "[X1 != d1 X1]" >::
        (fun () ->
           let x = var Logic "X" 1 ity in
           let d = const ~ts:1 "d" iity in
             assert_raises_occurs_check
               (fun () -> right_unify x (d ^^ [x]))) ;

      (* 10bis: quantifier dependency violation *)
      "[X1 a2 != d3 (X1 a2)]" >::
        (fun () ->
           let x = var Logic "X" 1 iity in
           let a = const ~ts:2 "a" ity in
           let d = const ~ts:3 "d" iity in
             assert_raises_unify_failure
               (fun () -> right_unify (x ^^ [a]) (d ^^ [x ^^ [a]]))) ;

      (* Example 11, flex-flex without raising *)
      "[X1 a2 b3 = Y1 b3 c3]" >::
        (fun () ->
           let x = var Logic "x" 1 (tyarrow [aty; bty] ity) in
           let y = var Logic "y" 1 (tyarrow [bty; cty] ity) in
           let a = const ~ts:2 "a" aty in
           let b = const ~ts:3 "b" bty in
           let c = const ~ts:3 "c" cty in
             right_unify (x ^^ [a;b]) (y ^^ [b;c]) ;
             let h =
               match extract [L;H] x with
                 | Var {name=h;ts=1;tag=Logic;ty=ty} -> var Logic h 1 ty
                 | _ -> failwith
                     (Printf.sprintf "X=%s should match Lam (_,(App H _))"
                        (term_to_string x))
             in
               assert_term_equal ([("a",aty); ("b",bty)] // (h ^^ [db 1])) x ;
               assert_term_equal ([("b",bty); ("c",cty)] // (h ^^ [db 2])) y) ;

      (* Example 12, flex-flex with raising on one var, pruning on the other *)
      "[X1 a2 b3 c3 = Y2 c3]" >::
        (fun () ->
           let x = var Logic "x" 1 (tyarrow [aty; bty; cty] ity) in
           let y = var Logic "y" 2 (tyarrow [cty] ity) in
           let a = const ~ts:2 "a" aty in
           let b = const ~ts:3 "b" bty in
           let c = const ~ts:3 "c" cty in
             right_unify (x ^^ [a;b;c]) (y ^^ [c]) ;
             let h =
               match extract [L;H] x with
                 | Var {name=h;ts=1;tag=Logic;ty=ty} -> var Logic h 1 ty
                 | _ -> failwith "X should match x\\y\\z\\ H ..."
             in
               assert_term_equal ([("a",aty); ("b",bty); ("c",cty)] // (h ^^ [db 3;db 1])) x ;
               assert_term_equal ([("c",cty)] // (h ^^ [a;db 1])) y) ;

      (* Example 13, flex-rigid where rigid has to be abstracted *)
      "[X1 a2 b3 = a2 (Y2 b3 c3)]" >::
        (fun () ->
           let x = var Logic "x" 1 (tyarrow [iity; bty] ity) in
           let y = var Logic "y" 2 (tyarrow [bty; cty] ity) in
           let a = const ~ts:2 "a" iity in
           let b = const ~ts:3 "b" bty in
           let c = const ~ts:3 "c" cty in
             right_unify (x ^^ [a;b]) (a ^^ [y ^^ [b;c]]) ;
             let h =
               match extract [L;A;H] x with
                 | Var {name=h;ts=1;tag=Logic;ty=ty} -> var Logic h 1 ty
                 | _ -> failwith "X should match x\\y\\ _ (H ..) .."
             in
               assert_term_equal
                 ([("a",iity); ("b",bty)] // (db 2 ^^ [h ^^ [db 2 ; db 1]])) x ;
               assert_term_equal
                 ([("b",bty); ("c",cty)] // (h ^^ [a ; db 2])) y) ;

      (* Example 14, rigid-path failure *)
      "[X1 a2 b3 != d3 (Y2 b3 c3)]" >::
        (fun () ->
           let x = var Logic "x" 1 (tyarrow [aty; bty] ity) in
           let y = var Logic "y" 2 (tyarrow [bty; cty] dty) in
           let a = const ~ts:2 "a" aty in
           let b = const ~ts:3 "b" bty in
           let c = const ~ts:3 "c" cty in
           let d = const ~ts:3 "d" (tyarrow [dty] ity) in
             assert_raises_unify_failure
               (fun () -> right_unify (x ^^ [a;b]) (d ^^ [y ^^ [b;c]]))) ;

      "[a = a]" >::
        (fun () ->
           right_unify (const ~ts:1 "a" aty) (const ~ts:1 "a" aty)) ;

      "[x\\ a x b = x\\ a x b]" >::
        (fun () ->
           let a = const ~ts:1 "a" (tyarrow [aty; bty] ity) in
           let b = const ~ts:1 "b" bty in
           let t = [("x",aty)] // ( a ^^ [ db 1 ; b ] ) in
             right_unify t t) ;

      (* End of Gopalan's examples *)

      "[f a a = f X X]" >::
        (fun () ->
           let f = const ~ts:1 "f" (tyarrow [aty; aty] ity) in
           let a = const ~ts:2 "a" aty in
           let x = var Logic "x" 3 aty in
             right_unify (f ^^ [x;x]) (f ^^ [a;a])) ;

      "[x\\y\\ P x = x\\ Q x]" >::
        (fun () ->
           let p = var Logic "P" 1 (tyarrow [aty] ity) in
           let q = var Logic "Q" 1 (tyarrow [aty; bty] ity) in
             right_unify
               ([("y",aty); ("x",bty)] // (p ^^ [db 2]))
               ([("x",aty)] // (q ^^ [db 1])) ;
             assert_term_equal ([("y",aty); ("x",bty)] // (p ^^ [db 2])) q) ;

      "[T = a X, T = a Y, Y = T]" >::
        (fun () ->
           let t = var Logic "T" 1 ity in
           let x = var Logic "X" 1 ity in
           let y = var Logic "Y" 1 ity in
           let a = const ~ts:0 "a" iity in
           let a x = a ^^ [x] in
             right_unify t (a x) ;
             right_unify t (a y) ;
             assert_raises_unify_failure
               (fun () -> right_unify y t)) ;

      "[x\\y\\ H1 x = x\\y\\ G2 x]" >::
        (fun () ->
           let h = var Logic "H" 1 (tyarrow [aty] ity) in
           let g = var Logic "G" 2 (tyarrow [aty] ity) in
             (* Different timestamps matter *)
             right_unify
               ([("y",aty); ("x",bty)] // (h ^^ [db 2]))
               ([("y",aty); ("x",bty)] // (g ^^ [db 2])) ;
             assert_term_equal (g^^[db 2]) (h^^[db 2])) ;

      "[X1 = y2]" >::
        (fun () ->
           let x = var Logic "X" 1 ity in
           let y = var Eigen "y" 2 ity in
             assert_raises_unify_failure
               (fun () -> right_unify x y)) ;

      (* Tests added while developing Abella *)
      "Saving and restoring states" >::
        (fun () ->
           let a = var Logic "A" 0 ity in
           let b = var Logic "B" 0 ity in
           let before = get_bind_state () in
             bind a b ;
             assert_term_pprint_equal "B" a ;
             assert_term_pprint_equal "B" b ;
             let after = get_bind_state () in
               set_bind_state before ;
               assert_term_pprint_equal "A" a ;
               assert_term_pprint_equal "B" b ;
               set_bind_state after ;
               assert_term_pprint_equal "B" a ;
               assert_term_pprint_equal "B" b) ;

      "No new names for simple unification" >::
        (fun () ->
           let a = var Logic "A" 0 aty in
           let b = var Logic "B" 0 bty in
           let m = var Logic "M" 0 cty in
           let n = var Logic "N" 0 dty in
           let v = var Logic "V" 0 bty in
           let ceval = const "eval" (tyarrow [aty; bty] ity) in
           let capp = const "app" (tyarrow [cty; dty] aty) in
           let evalAB = ceval ^^ [a; b] in
           let evalapp = ceval ^^ [capp ^^ [m; n]; v] in
             right_unify evalAB evalapp ;
             assert_term_pprint_equal "eval (app M N) V" evalAB) ;

      "[X = X]" >::
        (fun () ->
           let x = var Logic "X" 0 ity in
             right_unify x x ;
             assert_term_pprint_equal "X" x) ;

      "Loosening of LLambda restriction" >::
        (fun () ->
           let a = var Logic "A" 0 ity in
           let b = var Logic "B" 0 (tyarrow [cty] ity) in
           let c = var Logic "C" 0 cty in
             right_unify a (b ^^ [c]) ;
             assert_term_pprint_equal "B C" a) ;

      "Loosening of LLambda restriction inside of constructor" >::
        (fun () ->
           let a = var Logic "A" 0 aty in
           let b = var Logic "B" 0 (tyarrow [cty] bty) in
           let c = var Logic "C" 0 cty in
           let d = var Logic "D" 0 dty in
           let cons = const "cons" (tyarrow [bty; dty] aty) in
           let term = cons ^^ [b ^^ [c]; d] in
             right_unify a term ;
             assert_term_pprint_equal "cons (B C) D" a) ;

      "[X^0 = Y^1]" >::
        (fun () ->
           let x = var Logic "X" 0 ity in
           let y = var Logic "Y" 1 ity in
           let used = [("X", x); ("Y", y)] in
             right_unify ~used x y ;
             assert_term_pprint_equal "X" x ;
             assert_term_pprint_equal "X" y ;
             match observe x, observe y with
               | Var {ts=0; _}, Var {ts=0; _} -> ()
               | _ -> assert_failure "Timestamps should be lowered to match") ;

      "[X^0 = p^0 Y^1 Z^1]" >::
        (fun () ->
           let x = var Logic "X" 0 ity in
           let y = var Logic "Y" 1 ity in
           let z = var Logic "Z" 1 ity in
           let p = const "p" iiity in
           let used = [("X", x); ("Y", y); ("Z", z)] in
             right_unify ~used x (p ^^ [y; z]) ;
             assert_term_pprint_equal "p X1 X2" x ;
             match observe y, observe z with
               | Var {ts=0; _}, Var {ts=0; _} -> ()
               | _ -> assert_failure "Timestamps should be lowered to match") ;

      "X^0 = f^0 a^1" >::
        (fun () ->
           let a = const ~ts:1 "a" aty in
           let x = var Logic "X" 0 ity in
           let f = const "f" (tyarrow [aty] ity) in
           let used = [("X", x)] in
             assert_raises_unify_failure
               (fun () ->
                  right_unify ~used x (f ^^ [a]))) ;

      "Logic variables on right should not unify with nominal variables" >::
        (fun () ->
           let a = var Logic "A" 0 ity in
           let n = nominal_var "n" ity in
             assert_raises_any
               (fun () -> right_unify a n)) ;

      "Eigen variables on left should not unify with nominal variables" >::
        (fun () ->
           let a = var Eigen "a" 0 ity in
           let n = nominal_var "n" ity in
             assert_raises_any
               (fun () -> left_unify a n)) ;

      "Raised eigen variables on left should unify with nominal variables" >::
        (fun () ->
           let a = var Eigen "a" 0 iity in
           let n = nominal_var "n" ity in
             left_unify (a ^^ [n]) n ;
             assert_term_equal ([("a",ity)] // db 1) a) ;

      "Pruning should not generate a needless new name" >::
        (fun () ->
           let n = nominal_var "n" ity in
           let a = var Eigen "A" 0 (tyarrow [ity] aty) in
           let b = var Eigen "B" 0 aty in
           let used = [("A", a); ("B", b)] in
             left_unify ~used (a ^^ [n]) b ;
             assert_term_pprint_equal "x1\\B" a ;
             assert_term_pprint_equal "B" b) ;

      "X^0 a^1 b^1 = Y^0 Z^0 b^1" >::
        (fun () ->
           let a = const ~ts:1 "a" aty in
           let b = const ~ts:1 "b" bty in
           let x = var Eigen "X" 0 (tyarrow [aty; bty] ity) in
           let y = var Eigen "Y" 0 (tyarrow [cty; bty] ity) in
           let z = var Eigen "Z" 0 cty in
           let used = [("X", x); ("Y", y); ("Z", z)] in
             left_unify ~used (x ^^ [a;b]) (y ^^ [z;b]) ;
             assert_term_pprint_equal "x1\\x2\\Y Z x2" x ;
             assert_term_pprint_equal "Y" y ;
             assert_term_pprint_equal "Z" z) ;

      "X^0 a^1 = Y^0 (Z^0 a^1)" >::
        (fun () ->
           let a = const ~ts:1 "a" ity in
           let x = var Eigen "X" 0 iity in
           let y = var Eigen "Y" 0 iity in
           let z = var Eigen "Z" 0 iity in
           let used = [("X", x); ("Y", y); ("Z", z)] in
             left_unify ~used (x ^^ [a]) (y ^^ [z ^^ [a]]) ;
             assert_term_pprint_equal "x1\\Y (Z x1)" x ;
             assert_term_pprint_equal "Y" y ;
             assert_term_pprint_equal "Z" z) ;

      "w\\X^0 w = Y^0 Z^0" >::
        (fun () ->
           let x = var Eigen "X" 0 iity in
           let y = var Eigen "Y" 0 iiity in
           let z = var Eigen "Z" 0 ity in
           let used = [("X", x); ("Y", y); ("Z", z)] in
             left_unify ~used ([("w",ity)] // (x ^^ [db 1])) (y ^^ [z]) ;
             assert_term_pprint_equal "x1\\Y Z x1" x ;
             assert_term_pprint_equal "Y" y ;
             assert_term_pprint_equal "Z" z) ;

      "X^0 a^1 = app (Y^0 W^0 a^1) (Z^0 a^1)" >::
        (fun () ->
           let a = const ~ts:1 "a" aty in
           let x = var Eigen "X" 0 (tyarrow [aty] ity) in
           let y = var Eigen "Y" 0 (tyarrow [bty; aty] cty) in
           let z = var Eigen "Z" 0 (tyarrow [aty] dty) in
           let w = var Eigen "W" 0 bty in
           let capp = const "app" (tyarrow [cty; dty] ity) in
           let used = [("X", x); ("Y", y); ("Z", z); ("W", w)] in
             left_unify ~used
               (x ^^ [a])
               (capp ^^ [y ^^ [w;a]; z ^^ [a]]) ;
             assert_term_pprint_equal "x1\\app (Y W x1) (Z x1)" x ;
             assert_term_pprint_equal "W" w ;
             assert_term_pprint_equal "Y" y ;
             assert_term_pprint_equal "Z" z) ;

      "f\\x\\f x = f\\x\\f (Z f x)" >::
        (fun () ->
           let z = var Eigen "Z" 0 (tyarrow [iity; ity] ity) in
           let used = [("Z", z)] in
             left_unify ~used
               ([("x",iity); ("f",ity)] // (db 2 ^^ [db 1]))
               ([("x",iity); ("f",ity)] // (db 2 ^^ [z ^^ [db 2; db 1]])) ;
             assert_term_pprint_equal "x1\\x2\\x2" z) ;

      "p^0 (X^0 Y^0) = p^0 (Z^0 W^0)" >::
        (fun () ->
           let p = const ~ts:0 "p" iity in
           let x = var Logic "X" 0 iity in
           let y = var Logic "Y" 0 ity in
           let z = var Logic "Z" 0 iity in
           let w = var Logic "W" 0 ity in
             match try_right_unify_cpairs
               (p ^^ [x ^^ [y]])
               (p ^^ [z ^^ [w]])
             with
               | Some [(a,b)] ->
                   assert_term_pprint_equal "X Y" a ;
                   assert_term_pprint_equal "Z W" b
               | _ ->
                   assert_failure "Expected one conflict pair" );

      "p^0 (X^0 Y^0) = p^0 (z^0 w^0)" >::
        (fun () ->
           let p = const ~ts:0 "p" iity in
           let x = var Logic "X" 0 iity in
           let y = var Logic "Y" 0 ity in
           let z = var Eigen "z" 0 iity in
           let w = var Eigen "w" 0 ity in
             match try_right_unify_cpairs
               (p ^^ [x ^^ [y]])
               (p ^^ [z ^^ [w]])
             with
               | Some [(a,b)] ->
                   assert_term_pprint_equal "X Y" a ;
                   assert_term_pprint_equal "z w" b
               | Some l -> assert_failure
                   (Printf.sprintf "Expected one conflict pair, but found %d"
                      (List.length l))
               | None -> assert_failure "Unification failed" );

      "X^0 a^1 (Y^0 a^1) = Z^0" >::
        (fun () ->
           let x = var Logic "X" 0 iiity in
           let y = var Logic "Y" 0 iity in
           let z = var Logic "Z" 0 ity in
           let a = var Eigen "a" 1 ity in
             match try_right_unify_cpairs
               (x ^^ [a; y ^^ [a]]) z
             with
               | Some [(a,b)] ->
                   assert_term_pprint_equal "X a (Y a)" a ;
                   assert_term_pprint_equal "Z" b
               | Some l -> assert_failure
                   (Printf.sprintf "Expected one conflict pair, but found %d"
                      (List.length l))
               | None -> assert_failure "Unification failed" );

      "x1\\p^0 (X^0 x1 (Y^0 x1)) = x1\\p^0 Z^0" >::
        (fun () ->
           let p = const ~ts:0 "p" iity in
           let x = var Logic "X" 0 iiity in
           let y = var Logic "Y" 0 iity in
           let z = var Logic "Z" 0 ity in
             match try_right_unify_cpairs
               ([("x1",ity)] // (p ^^ [x ^^ [db 1; y ^^ [db 1]]]))
               ([("x1",ity)] // (p ^^ [z]))
             with
               | Some [(a,b)] ->
                   assert_term_pprint_equal "x1\\X x1 (Y x1)" a ;
                   assert_term_pprint_equal "x1\\Z" b
               | Some l -> assert_failure
                   (Printf.sprintf "Expected one conflict pair, but found %d"
                      (List.length l))
               | None -> assert_failure "Unification failed" );

      "X^0 = F^0 X^0" >::
        (fun () ->
           let x = var Logic "X" 0 ity in
           let f = var Logic "F" 0 iity in
             match try_right_unify_cpairs x (f ^^ [x]) with
               | Some [(a, b)] ->
                   assert_term_pprint_equal "X" a ;
                   assert_term_pprint_equal "F X" b ;
               | Some l -> assert_failure
                   (Printf.sprintf "Expected one conflict pair, but found %d"
                      (List.length l))
               | None -> assert_failure "Unification failed" );

      "X^0 = x1\\Y^1" >::
        (fun () ->
           let x = var Logic "X" 0 iity in
           let y = var Logic "Y" 1 ity in
           let used = [("X", x); ("Y", y)] in
             right_unify ~used x ([("x1",ity)] // y) ;
             assert_term_pprint_equal "x1\\Y1" x ;
             match observe y with
               | Var {ts=0; _} -> ()
               | _ -> assert_failure "Timestamp should be lowered to match") ;

      "R^0 N^0 = plus A^0 B^0" >::
        (fun () ->
           let r = var Eigen "R" 0 iity in
           let n = var Eigen "N" 0 ity in
           let a = var Eigen "A" 0 ity in
           let b = var Eigen "B" 0 ity in
           let plus = var Constant "plus" 0 iiity in
           let used = [("R", r); ("N", n); ("A", a); ("B", b)] in
             match
               left_flexible_heads ~used ~sr:Subordination.empty
                 ([], r, [n]) ([], plus, [a; b])
             with
               | [t1; t2] ->
                   assert_term_pprint_equal "x1\\plus (R1 x1) (R2 x1)" t1 ;
                   assert_term_pprint_equal "x1\\x1" t2 ;
               | ts ->
                   assert_int_equal 2 (List.length ts)
        );

      "R^0 N^0 = x1\\x1 A^0 B^0" >::
        (fun () ->
           let r = var Eigen "R" 0 (tyarrow [ity; iiity] ity) in
           let n = var Eigen "N" 0 ity in
           let a = var Eigen "A" 0 ity in
           let b = var Eigen "B" 0 ity in
           let used = [("R", r); ("N", n); ("A", a); ("B", b)] in
             match
               left_flexible_heads ~used ~sr:Subordination.empty
                 ([], r, [n]) ([("x1",iiity)], db 1, [a; b])
             with
               | [t1; t2] ->
                   assert_term_pprint_equal
                     "x1\\x2\\x2 (R1 x1 x2) (R2 x1 x2)" t1 ;
                   assert_term_pprint_equal
                     "x1\\x2\\x1" t2 ;
               | ts ->
                   assert_int_equal 2 (List.length ts)
        );

      "x1\\R^0 N^0 = x1\\x1 A^0 B^0" >::
        (fun () ->
           let r = var Eigen "R" 0 iity in
           let n = var Eigen "N" 0 ity in
           let a = var Eigen "A" 0 ity in
           let b = var Eigen "B" 0 ity in
           let used = [("R", r); ("N", n); ("A", a); ("B", b)] in
             match
               left_flexible_heads ~used ~sr:Subordination.empty
                 ([("x1",iiity)], r, [n]) ([("x1",iiity)], db 1, [a; b])
             with
               | [t1] ->
                   assert_term_pprint_equal "x1\\x1" t1 ;
               | ts ->
                   assert_int_equal 1 (List.length ts)
        );

      "R^0 X^0 b^0 = a^0 b^0" >::
        (fun () ->
           let r = var Eigen "R" 0 (tyarrow [iiity; ity] ity) in
           let x = var Eigen "X" 0 iiity in
           let a = var Constant "a" 0 iity in
           let b = var Constant "b" 0 ity in
           let used = [("R", r); ("X", x); ("A", a); ("B", b)] in
             match
               left_flexible_heads ~used ~sr:Subordination.empty
                 ([], r, [x; b]) ([], a, [b])
             with
               | [t1; t2; t3] ->
                   assert_term_pprint_equal
                     "x1\\x2\\a (R1 x1 x2)" t1 ;
                   assert_term_pprint_equal
                     "x1\\x2\\x1 (R1 x1 x2) (R2 x1 x2)" t2 ;
                   assert_term_pprint_equal
                     "x1\\x2\\x2" t3 ;
               | ts ->
                   assert_int_equal 3 (List.length ts)
        );

      "Flex-rigid subordination: R A1 B1 = sr_a_b A2 B2" >::
        (fun () ->
           let r = var Eigen "R" 0 (tyarrow [sr_a; sr_b] oty) in
           let a1 = var Eigen "A1" 0 sr_a in
           let a2 = var Eigen "A2" 0 sr_a in
           let b1 = var Eigen "B1" 0 sr_b in
           let b2 = var Eigen "B2" 0 sr_b in
           let sr_a_b = var Constant "sr_a_b" 0 (tyarrow [sr_a; sr_b] oty) in
           let used =
             [("R", r); ("A1", a1); ("A2", a2); ("B1", b1); ("B2", b2)]
           in
             match
               left_flexible_heads ~used ~sr:sr_sr
                 ([], r, [a1; b1]) ([], sr_a_b, [a2; b2])
             with
               | [t1] ->
                   assert_term_pprint_equal
                     "x1\\x2\\sr_a_b (R1 x1) (R2 x1 x2)" t1 ;
               | ts ->
                   assert_int_equal 1 (List.length ts)
        );

      "X = f\\f (X (y\\e))" >::
        (fun () ->
           let xty = tyarrow [iity] ity in
           let x = var Logic "X" 0 xty in
           let e = var Constant "e" 0 ity in
             match
               try_right_unify_cpairs
                 x
                 ([("f",iity)] // (db 1 ^^ [x ^^ [[("y",ity)] // e]]))
             with
               | Some [(a, b)] ->
                   assert_term_pprint_equal "X" a ;
                   assert_term_pprint_equal "x1\\x1 (X x2\\e)" b ;
               | Some l -> assert_failure
                   (Printf.sprintf "Expected one conflict pair, but found %d"
                      (List.length l))
               | None ->
                   (* X = f\ f e is one solution *)
                   assert_failure "Unification failed"
        );

      (* This is a case where unification has no most general
         solution, but it would be nice of a partial solution was at
         least generated. Perhaps more generally we could eventually
         treat all higher-order unification problems (perhaps with a
         special tactic to invoke such solution finding)

      "X^0 = Y^0 a^1 (Z^0 a^1)" >::
        (fun () ->
           let a = const ~ts:1 "a" ity in
           let x = var Eigen "X" 0 ity in
           let y = var Eigen "Y" 0 iiity in
           let z = var Eigen "Z" 0 iity in
             match try_right_unify_cpairs
               x
               (y ^^ [a; z ^^ [a]])
             with
               | Some [(t1,t2)] ->
                   assert_term_pprint_equal "X" t1 ;
                   assert_term_pprint_equal "Y1 (Z a)" t2
               | Some l -> assert_failure
                   (Printf.sprintf "Expected one conflict pair, but found %d"
                      (List.length l))
               | None -> assert_failure "Unification failed" );

      *)

    ]
