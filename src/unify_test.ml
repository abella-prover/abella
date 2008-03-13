open OUnit
open Term
open Term.Notations
open Test_helper
open Unify

(* Extracting a variable at some position in a term,
 * used when we know a variable should be there, but don't know what it is
 * since it's fresh. *)
type path = L | A | H
let rec extract path t =
  let hd,tl = match path with h::t -> h,t | [] -> assert false in
    match !!t with
      | Lam (_,t) when hd = L -> extract tl t
      | App (_,l) when hd = A -> extract tl (List.nth l 0)
      | App (t,_) when hd = H -> !!t
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
           let t1 = 1 // db 1 in
           let m = var Logic "m" 1 in
           let t2 = 1 // ( m ^^ [ db 1 ] ) in
             right_unify t1 t2 ;
             assert_term_equal (1 // db 1) m) ;

      (* Example 2, adds descending into constructors *)
      "[x\\ c x = x\\ c (N x)]" >::
        (fun () ->
           let n = var Logic "n" 1 in
           let c = const ~ts:1 "c" in
           let t1 = 1 // (c ^^ [ db 1 ]) in
           let t2 = 1 // (c ^^ [ n ^^ [ db 1 ] ]) in
             right_unify t1 t2 ;
             assert_term_equal (1 // db 1) n) ;

      (* Example 3, needs eta expanding on the fly *)
      "[x\\y\\ c y x = N]" >::
        (fun () ->
           let n = var Logic "n" 1 in
           let c = const ~ts:1 "c" in
           let t = 2 // (c ^^ [ db 1 ; db 2 ]) in
             right_unify t n ;
             assert_term_equal (2 // (c ^^ [ db 1 ; db 2 ])) n) ;

      (* Example 4, on-the-fly eta, constructors at top-level *)
      "[x\\y\\ c x y = x\\ c (N x)]" >::
        (fun () ->
           let n = var Logic "n" 1 in
           let c = const ~ts:1 "c" in
             right_unify (2 // (c ^^ [db 2;db 1])) (1 // (c ^^ [n ^^ [db 1]])) ;
             assert_term_equal (1 // db 1) n) ;

      (* Example 5, flex-flex case where we need to raise & prune *)
      "[X1 a2 b3 = Y2 b3 c3]" >::
        (fun () ->
           let x = var Logic "x" 1 in
           let y = var Logic "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
           let t1 = x ^^ [ a ; b ] in
           let t2 = y ^^ [ b ; c ] in
             right_unify t1 t2 ;
             let h =
               let x = hnorm x in
                 match extract [L;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var Logic h 1
                   | _ -> assert_failure "X should match x\\y\\ H ..."
             in
               assert_term_equal (2 // (h ^^ [ db 2 ; db 1 ])) x ;
               assert_term_equal (2 // (h ^^ [ a ; db 2 ])) y) ;

      (* Example 6, flex-rigid case involving raise & prune relative to an
       * embedded flex term. *)
      "[X1 a2 b3 = c1 (Y2 b3 c3)]" >::
        (fun () ->
           let x = var Logic "x" 1 in
           let y = var Logic "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:1 "c" in
           let c3 = const ~ts:3 "c" in
             right_unify (x ^^ [a;b]) (c ^^ [y ^^ [b;c3]]) ;
             let h =
               let x = hnorm x in
                 match extract [L;A;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var Logic h 1
                   | _ -> assert_failure "X should match x\\y\\ _ H .."
             in
               assert_term_equal (2 // (c ^^ [h^^[db 2;db 1]])) x ;
               assert_term_equal (2 // (h ^^ [a;db 2])) y) ;

      (* Example 7, multiple occurences *)
      "[c1 (X1 a2 b3) (X b3 d2) = c1 (Y2 b3 c3) (b3 d2)]" >::
        (fun () ->
           let x = var Logic "x" 1 in
           let y = var Logic "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
           let d = const ~ts:2 "d" in
             right_unify
               (c ^^ [ x ^^ [a;b] ; x ^^ [b;d] ])
               (c ^^ [ y ^^ [b;c] ; b ^^ [d] ]) ;
             assert_term_equal (2 // (db 2 ^^ [db 1])) x ;
             assert_term_equal (2 // (a ^^ [db 2])) y) ;

      (* Example 8, multiple occurences with a bound var as the rigid part
       * instead of a constant *)
      "[x\\ c1 (X1 a2 b3) (X x d2) = x\\ c1 (Y2 b3 c3) (x d2)]" >::
        (fun () ->
           let x = var Logic "x" 1 in
           let y = var Logic "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let d = const ~ts:2 "d" in
           let c = const ~ts:3 "c" in
             right_unify
               (1 // (c ^^ [ x ^^ [a;b] ; x ^^ [db 1;d]]))
               (1 // (c ^^ [ y ^^ [b;c] ; db 1 ^^ [d] ])) ;
             assert_term_equal (2 // (db 2 ^^ [db 1])) x ;
             assert_term_equal (2 // (a ^^ [db 2])) y) ;

      (* Example 9, flex-flex with same var at both heads *)
      "[X1 a2 b3 c3 = X1 c3 b3 a2]" >::
        (fun () ->
           let x = var Logic "x" 1 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
             right_unify (x ^^ [a;b;c]) (x ^^ [c;b;a]) ;
             let h =
               let x = hnorm x in
                 match extract [L;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var Logic h 1
                   | _ -> assert_failure "X should match x\\y\\z\\ H ..."
             in
               assert_term_equal (3 // (h^^[db 2])) x) ;

      (* Example 10, failure due to OccursCheck *)
      "[X1 a2 b3 != c1 (X1 b3 c3)]" >::
        (fun () ->
           let x = var Logic "x" 1 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c1 = const ~ts:1 "c" in
           let c3 = const ~ts:3 "c" in
             assert_raises_occurs_check
               (fun () -> right_unify (x ^^ [a;b]) (c1 ^^ [x ^^ [b;c3]]))) ;

      (* 10bis: quantifier dependency violation -- raise OccursCheck too *)
      "[X1 a2 b3 != c3 (X b3 c3)]" >::
        (fun () ->
           let x = var Logic "x" 1 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
             assert_raises_occurs_check
               (fun () -> right_unify (x ^^ [a;b]) (c ^^ [x ^^ [b;c]]))) ;

      (* Example 11, flex-flex without raising *)
      "[X1 a2 b3 = Y1 b3 c3]" >::
        (fun () ->
           let x = var Logic "x" 1 in
           let y = var Logic "y" 1 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
             right_unify (x ^^ [a;b]) (y ^^ [b;c]) ;
             let h =
               let x = hnorm x in
                 match extract [L;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var Logic h 1
                   | _ -> failwith
                       (Printf.sprintf "X=%s should match Lam (_,(App H _))"
                          (term_to_string x))
             in
               assert_term_equal (2 // (h ^^ [db 1])) x ;
               assert_term_equal (2 // (h ^^ [db 2])) y) ;

      (* Example 12, flex-flex with raising on one var, pruning on the other *)
      "[X1 a2 b3 c3 = Y2 c3]" >::
        (fun () ->
           let x = var Logic "x" 1 in
           let y = var Logic "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
             right_unify (x ^^ [a;b;c]) (y ^^ [c]) ;
             let h =
               let x = hnorm x in
                 match extract [L;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var Logic h 1
                   | _ -> failwith "X should match x\\y\\z\\ H ..."
             in
               assert_term_equal (3 // (h ^^ [db 3;db 1])) x ;
               assert_term_equal (1 // (h ^^ [a;db 1])) y) ;

      (* Example 13, flex-rigid where rigid has to be abstracted *)
      "[X1 a2 b3 = a2 (Y2 b3 c3)]" >::
        (fun () ->
           let x = var Logic "x" 1 in
           let y = var Logic "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
             right_unify (x ^^ [a;b]) (a ^^ [y ^^ [b;c]]) ;
             let h =
               let x = hnorm x in
                 match extract [L;A;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var Logic h 1
                   | _ -> failwith "X should match x\\y\\ _ (H ..) .."
             in
               assert_term_equal (2 // (db 2 ^^ [h ^^ [db 2 ; db 1]])) x ;
               assert_term_equal (2 // (h ^^ [a ; db 2])) y) ;

      (* Example 14, OccursCheck *)
      "[X1 a2 b3 != d3 (Y2 b3 c3)]" >::
        (fun () ->
           let x = var Logic "x" 1 in
           let y = var Logic "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
           let d = const ~ts:3 "d" in
             assert_raises_occurs_check
               (fun () -> right_unify (x ^^ [a;b]) (d ^^ [y ^^ [b;c]]))) ;

      "[a = a]" >::
        (fun () ->
           right_unify (const ~ts:1 "a") (const ~ts:1 "a")) ;

      "[x\\ a x b = x\\ a x b]" >::
        (fun () ->
           let a = const ~ts:1 "a" in
           let b = const ~ts:1 "b" in
           let t = 1 // ( a ^^ [ db 1 ; b ] ) in
             right_unify t t) ;

      (* End of Gopalan's examples *)

      "[f\\ a a = f\\ X X]" >::
        (fun () ->
           let a = const ~ts:2 "a" in
           let f = const ~ts:1 "f" in
           let x = var Logic "x" 3 in
             right_unify (f ^^ [x;x]) (f ^^ [a;a])) ;

      "[x\\x1\\ P x = x\\ Q x]" >::
        (fun () ->
           let p = var Logic "P" 1 in
           let q = var Logic "Q" 1 in
             right_unify (2 // (p ^^ [db 2])) (1 // (q ^^ [db 1])) ;
             assert_term_equal (2 // (p ^^ [db 2])) q) ;

      "[T = a X, T = a Y, Y = T]" >::
        (fun () ->
           let t = var Logic "T" 1 in
           let x = var Logic "X" 1 in
           let y = var Logic "Y" 1 in
           let a = const ~ts:0 "a" in
           let a x = a ^^ [x] in
             right_unify t (a x) ;
             right_unify t (a y) ;
             assert_raises_unify_failure
               (fun () -> right_unify y t)) ;

      "[x\\y\\ H1 x = x\\y\\ G2 x]" >::
        (fun () ->
           let h = var Logic "H" 1 in
           let g = var Logic "G" 2 in
             (* Different timestamps matter *)
             right_unify (2// (h ^^ [db 2])) (2// (g ^^ [db 2])) ;
             assert_term_equal (g^^[db 2]) (h^^[db 2])) ;

      "[X1 = y2]" >::
        (fun () ->
           let x = var Logic "X" 1 in
           let y = var Eigen "y" 2 in
             assert_raises_unify_failure
               (fun () -> right_unify x y)) ;

      (* Tests added while developing Abella *)
      "Saving and restoring states" >::
        (fun () ->
           let a = var Logic "A" 0 in
           let b = var Logic "B" 0 in
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
           let a = var Logic "A" 0 in
           let b = var Logic "B" 0 in
           let m = var Logic "M" 0 in
           let n = var Logic "N" 0 in
           let v = var Logic "V" 0 in
           let ceval = const "eval" in
           let capp = const "app" in
           let evalAB = app ceval [a; b] in
           let evalapp = app ceval [app capp [m; n]; v] in
             right_unify evalAB evalapp ;
             assert_term_pprint_equal "eval (app M N) V" evalAB) ;
      
      "[X = X]" >::
        (fun () ->
           let x = var Logic "X" 0 in
             right_unify x x ;
             assert_term_pprint_equal "X" x) ;
      
      "Loosening of LLambda restriction" >::
        (fun () ->
           let a = var Logic "A" 0 in
           let b = var Logic "B" 0 in
           let c = var Logic "C" 0 in
             right_unify a (app b [c]) ;
             assert_term_pprint_equal "B C" a) ;

      "Loosening of LLambda restriction inside of constructor" >::
        (fun () ->
           let a = var Logic "A" 0 in
           let b = var Logic "B" 0 in
           let c = var Logic "C" 0 in
           let d = var Logic "D" 0 in
           let term = app (const "cons") [app b [c]; d] in
             right_unify a term ;
             assert_term_pprint_equal "cons (B C) D" a) ;

      (** This bug was pointed out by David. We should address it once we
          start dealing more with timestamps. But there are also other
          changes we made to unify which neglect timestamps
          
      "[X^0 = Y^1]" >::
        (fun () ->
           let x = var Logic "X" 0 in
           let y = var Logic "Y" 1 in
             right_unify x y ;
             match !!x,!!y with
               | Var {ts=0}, Var {ts=0} -> ()
               | _ -> assert_failure "Timestamps should be lowered to match") ;
      *)

      "X^0 = f^0 a^1" >::
        (fun () ->
           let a = const ~ts:1 "a" in
           let x = var Logic "X" 0 in
           let used = [("X", x)] in
             assert_raises_unify_failure
               (fun () ->
                  right_unify ~used x (app (const "f") [a]))) ;
             
      "Logic variables on right should not unify with nominal variables" >::
        (fun () ->
           let a = var Logic "A" 0 in
           let n = nominal_var "n" in
             assert_raises_any
               (fun () -> right_unify a n)) ;

      "Eigen variables on left should not unify with nominal variables" >::
        (fun () ->
           let a = var Eigen "a" 0 in
           let n = nominal_var "n" in
             assert_raises_any
               (fun () -> left_unify a n)) ;

      "Raised eigen variables on left should unify with nominal variables" >::
        (fun () ->
           let a = var Eigen "a" 0 in
           let n = nominal_var "n" in
             left_unify (app a [n]) n ;
             assert_term_equal (1 // db 1) a) ;

      "Pruning should not generate a needless new name" >::
        (fun () ->
           let n = nominal_var "n" in
           let a = var Eigen "A" 0 in
           let b = var Eigen "B" 0 in
           let used = [("A", a); ("B", b)] in
             left_unify ~used (app a [n]) b ;
             assert_term_pprint_equal "x1\\B" a ;
             assert_term_pprint_equal "B" b) ;

      "X^0 a^1 b^1 = Y^0 Z^0 b^1" >::
        (fun () ->
           let a = const ~ts:1 "a" in
           let b = const ~ts:1 "b" in
           let x = var Eigen "X" 0 in
           let y = var Eigen "Y" 0 in
           let z = var Eigen "Z" 0 in
           let used = [("X", x); ("Y", y); ("Z", z)] in
             left_unify ~used (app x [a;b]) (app y [z;b]) ;
             assert_term_pprint_equal "x1\\x2\\Y Z x2" x ;
             assert_term_pprint_equal "Y" y ;
             assert_term_pprint_equal "Z" z) ;
             
      "X^0 a^1 = Y^0 (Z^0 a^1)" >::
        (fun () ->
           let a = const ~ts:1 "a" in
           let x = var Eigen "X" 0 in
           let y = var Eigen "Y" 0 in
           let z = var Eigen "Z" 0 in
           let used = [("X", x); ("Y", y); ("Z", z)] in
             left_unify ~used (app x [a]) (app y [app z [a]]) ;
             assert_term_pprint_equal "x1\\Y (Z x1)" x ;
             assert_term_pprint_equal "Y" y ;
             assert_term_pprint_equal "Z" z) ;

    ]
