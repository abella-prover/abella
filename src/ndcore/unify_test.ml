open OUnit
open Term
open Term.Notations
open Ndcore_test

let unify =
  let module Unify =
    Unify.Make (struct
                  let instantiatable = Logic
                  let constant_like  = Eigen
                end)
  in
    Unify.unify
      
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
      | _ -> Var {name="notfound";ts=0;tag=Constant}
          
(* Tests from Nadathur's SML implementation *)
let tests =
  "Unify" >:::
    [
      (* Example 1, simple test involving abstractions *)
      "[x\\ x = x\\ M x]" >::
        (fun () ->
           let t1 = 1 // db 1 in
           let m = var "m" 1 in
           let t2 = 1 // ( m ^^ [ db 1 ] ) in
             unify t1 t2 ;
             assert_term_equal (1 // db 1) m) ;

      (* Example 2, adds descending into constructors *)
      "[x\\ c x = x\\ c (N x)]" >::
        (fun () ->
           let n = var "n" 1 in
           let c = const ~ts:1 "c" in
           let t1 = 1 // (c ^^ [ db 1 ]) in
           let t2 = 1 // (c ^^ [ n ^^ [ db 1 ] ]) in
             unify t1 t2 ;
             assert_term_equal (1 // db 1) n) ;

      (* Example 3, needs eta expanding on the fly *)
      "[x\\y\\ c y x = N]" >::
        (fun () ->
           let n = var "n" 1 in
           let c = const ~ts:1 "c" in
           let t = 2 // (c ^^ [ db 1 ; db 2 ]) in
             unify t n ;
             assert_term_equal (2 // (c ^^ [ db 1 ; db 2 ])) n) ;

      (* Example 4, on-the-fly eta, constructors at top-level *)
      "[x\\y\\ c x y = x\\ c (N x)]" >::
        (fun () ->
           let n = var "n" 1 in
           let c = const ~ts:1 "c" in
             unify (2 // (c ^^ [db 2;db 1])) (1 // (c ^^ [n ^^ [db 1]])) ;
             assert_term_equal (1 // db 1) n) ;

      (* Example 5, flex-flex case where we need to raise & prune *)
      "[X1 a2 b3 = Y2 b3 c3]" >::
        (fun () ->
           let x = var "x" 1 in
           let y = var "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
           let t1 = x ^^ [ a ; b ] in
           let t2 = y ^^ [ b ; c ] in
             unify t1 t2 ;
             let h =
               let x = Norm.hnorm x in
                 match extract [L;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var h 1
                   | _ -> failwith "X should match x\\y\\ H ..."
             in
               assert_term_equal (2 // (h ^^ [ db 2 ; db 1 ])) x ;
               assert_term_equal (2 // (h ^^ [ a ; db 2 ])) y) ;

      (* Example 6, flex-rigid case involving raise & prune relative to an
       * embedded flex term. *)
      "[X1 a2 b3 = c1 (Y2 b3 c3)]" >::
        (fun () ->
           let x = var "x" 1 in
           let y = var "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:1 "c" in
           let c3 = const ~ts:3 "c" in
             unify (x ^^ [a;b]) (c ^^ [y ^^ [b;c3]]) ;
             let h =
               let x = Norm.hnorm x in
                 match extract [L;A;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var h 1
                   | _ -> failwith "X should match x\\y\\ _ H .."
             in
               assert_term_equal (2 // (c ^^ [h^^[db 2;db 1]])) x ;
               assert_term_equal (2 // (h ^^ [a;db 2])) y) ;

      (* Example 7, multiple occurences *)
      "[c1 (X1 a2 b3) (X b3 d2) = c1 (Y2 b3 c3) (b3 d2)]" >::
        (fun () ->
           let x = var "x" 1 in
           let y = var "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
           let d = const ~ts:2 "d" in
             unify
               (c ^^ [ x ^^ [a;b] ; x ^^ [b;d] ])
               (c ^^ [ y ^^ [b;c] ; b ^^ [d] ]) ;
             assert_term_equal (2 // (db 2 ^^ [db 1])) x ;
             assert_term_equal (2 // (a ^^ [db 2])) y) ;

      (* Example 8, multiple occurences with a bound var as the rigid part
       * instead of a constant *)
      "[x\\ c1 (X1 a2 b3) (X x d2) = x\\ c1 (Y2 b3 c3) (x d2)]" >::
        (fun () ->
           let x = var "x" 1 in
           let y = var "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let d = const ~ts:2 "d" in
           let c = const ~ts:3 "c" in
             unify
               (1 // (c ^^ [ x ^^ [a;b] ; x ^^ [db 1;d]]))
               (1 // (c ^^ [ y ^^ [b;c] ; db 1 ^^ [d] ])) ;
             assert_term_equal (2 // (db 2 ^^ [db 1])) x ;
             assert_term_equal (2 // (a ^^ [db 2])) y) ;

      (* Example 9, flex-flex with same var at both heads *)
      "[X1 a2 b3 c3 = X1 c3 b3 a2]" >::
        (fun () ->
           let x = var "x" 1 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
             unify (x ^^ [a;b;c]) (x ^^ [c;b;a]) ;
             let h =
               let x = Norm.hnorm x in
                 match extract [L;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var h 1
                   | _ -> failwith "X should match x\\y\\z\\ H ..."
             in
               assert_term_equal (3 // (h^^[db 2])) x) ;

      (* Example 10, failure due to OccursCheck
       * TODO Are the two different timestamps wanted for c ? *)
      "[X1 a2 b3 != c1 (X1 b3 c3)]" >::
        (fun () ->
           let x = var "x" 1 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c1 = const ~ts:1 "c" in
           let c3 = const ~ts:3 "c" in
             try
               unify (x ^^ [a;b]) (c1 ^^ [x ^^ [b;c3]]) ;
               "Expected OccursCheck" @? false
             with
               | Unify.Error Unify.OccursCheck -> ()) ;

      (* 10bis: quantifier dependency violation -- raise OccursCheck too *)
      "[X1 a2 b3 != c3 (X b c)]" >::
        (fun () ->
           let x = var "x" 1 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
             try
               unify (x ^^ [a;b]) (c ^^ [x ^^ [b;c]]) ;
               "Expected OccursCheck" @? false
             with
               | Unify.Error Unify.OccursCheck -> ()) ;

      (* Example 11, flex-flex without raising *)
      "[X1 a2 b3 = Y1 b3 c3]" >::
        (fun () ->
           let x = var "x" 1 in
           let y = var "y" 1 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
             unify (x ^^ [a;b]) (y ^^ [b;c]) ;
             let h =
               let x = Norm.hnorm x in
                 match extract [L;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var h 1
                   | _ -> failwith
                       (Printf.sprintf "X=%s should match Lam (_,(App H _))"
                          (Pprint.term_to_string x))
             in
               assert_term_equal (2 // (h ^^ [db 1])) x ;
               assert_term_equal (2 // (h ^^ [db 2])) y) ;

      (* Example 12, flex-flex with raising on one var, pruning on the other *)
      "[X1 a2 b3 c3 = Y2 c3]" >::
        (fun () ->
           let x = var "x" 1 in
           let y = var "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
             unify (x ^^ [a;b;c]) (y ^^ [c]) ;
             let h =
               let x = Norm.hnorm x in
                 match extract [L;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var h 1
                   | _ -> failwith "X should match x\\y\\z\\ H ..."
             in
               assert_term_equal (3 // (h ^^ [db 3;db 1])) x ;
               assert_term_equal (1 // (h ^^ [a;db 1])) y) ;

      (* Example 13, flex-rigid where rigid has to be abstracted *)
      "[X1 a2 b3 = a2 (Y2 b3 c3)]" >::
        (fun () ->
           let x = var "x" 1 in
           let y = var "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
             unify (x ^^ [a;b]) (a ^^ [y ^^ [b;c]]) ;
             let h =
               let x = Norm.hnorm x in
                 match extract [L;A;H] x with
                   | Var {name=h;ts=1;tag=Logic} -> var h 1
                   | _ -> failwith "X should match x\\y\\ _ (H ..) .."
             in
               assert_term_equal (2 // (db 2 ^^ [h ^^ [db 2 ; db 1]])) x ;
               assert_term_equal (2 // (h ^^ [a ; db 2])) y) ;

      (* Example 14, OccursCheck *)
      "[X1 a2 b3 != d3 (Y2 b3 c3)]" >::
        (fun () ->
           let x = var "x" 1 in
           let y = var "y" 2 in
           let a = const ~ts:2 "a" in
           let b = const ~ts:3 "b" in
           let c = const ~ts:3 "c" in
           let d = const ~ts:3 "d" in
             try
               unify (x ^^ [a;b]) (d ^^ [y ^^ [b;c]]) ;
               "Expected OccursCheck" @? false
             with
               | Unify.Error Unify.OccursCheck -> ()) ;

      "[a = a]" >::
        (fun () ->
           unify (const ~ts:1 "a") (const ~ts:1 "a")) ;

      "[x\\ a x b = x\\ a x b]" >::
        (fun () ->
           let a = const ~ts:1 "a" in
           let b = const ~ts:1 "b" in
           let t = 1 // ( a ^^ [ db 1 ; b ] ) in
             unify t t) ;

      (* End of Gopalan's examples *)

      "[f\\ a a = f\\ X X]" >::
        (fun () ->
           let a = const ~ts:2 "a" in
           let f = const ~ts:1 "f" in
           let x = var "x" 3 in
             unify (f ^^ [x;x]) (f ^^ [a;a])) ;

      "[x\\x1\\ P x = x\\ Q x]" >::
        (fun () ->
           let p = var "P" 1 in
           let q = var "Q" 1 in
             unify (2 // (p ^^ [db 2])) (1 // (q ^^ [db 1])) ;
             assert_term_equal (2 // (p ^^ [db 2])) q) ;

      (* This one used to fail, I don't remember having fixed it consciously.. *)
      "[T = a X, T = a Y, Y = T]" >::
        (fun () ->
           let t = var "T" 1 in
           let x = var "X" 1 in
           let y = var "Y" 1 in
           let a = const ~ts:0 "a" in
           let a x = a ^^ [x] in
             unify t (a x) ;
             unify t (a y) ;
             begin try unify y t ; assert false with
               | Unify.Error _ -> () end) ;

      (* This one used to fail, but the bug is fixed *)
      "[x\\y\\ H1 x = x\\y\\ G2 x]" >::
        (fun () ->
           let h = var "H" 1 in
           let g = var "G" 2 in
             (* Different timestamps matter *)
             unify (2// (h ^^ [db 2])) (2// (g ^^ [db 2])) ;
             assert_term_equal (g^^[db 2]) (h^^[db 2])) ;

      "[X1 = y2]" >::
        (fun () ->
           let x = var "X" 1 in
           let y = var ~tag:Eigen "y" 2 in
             try unify x y ; assert false with
               | Unify.Error _ -> ()) ;

      "Saving and restoring states and substs" >::
        (fun () ->
           let a = var "A" 0 in
           let b = var "B" 0 in
           let state = save_state () in
             bind a b ;
             assert_pprint_equal "B" a ;
             assert_pprint_equal "B" b ;
             let subst = get_subst state in
               restore_state state ;
               assert_pprint_equal "A" a ;
               assert_pprint_equal "B" b ;
               apply_subst subst ;
               assert_pprint_equal "B" a ;
               assert_pprint_equal "B" b) ;

      "No new names for simple unification" >::
        (fun () ->
           let a = var "A" 0 in
           let b = var "B" 0 in
           let m = var "M" 0 in
           let n = var "N" 0 in
           let v = var "V" 0 in
           let ceval = const "eval" in
           let capp = const "app" in
           let evalAB = app ceval [a; b] in
           let evalapp = app ceval [(app capp [m; n]); v] in
             unify evalAB evalapp ;
             assert_pprint_equal "eval (app M N) V" evalAB) ;
      
    ]
