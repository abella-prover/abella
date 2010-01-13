open OUnit
open Term
open Term.Notations
open Extensions
open Test_helper

let norm_tests =
  "Norm" >:::
    [
      "[(x\\ x) c]" >::
        (fun () ->
           let c = uconst "c" in
           let t = (1 /// db 1) ^^ [c] in
           let t = hnorm t in
             assert_term_equal c t) ;

      "[(x\\ y\\ x) a b]" >::
        (fun () ->
           let a = uconst "a" in
           let b = uconst "b" in
           let t = (2 /// db 2) ^^ [a; b] in
           let t = hnorm t in
             assert_term_equal a t) ;

      "[(x\\ y\\ y) a b]" >::
        (fun () ->
           let a = uconst "a" in
           let b = uconst "b" in
           let t = (2 /// db 1) ^^ [a; b] in
           let t = hnorm t in
             assert_term_equal b t) ;

      "[(x\\ y\\ z\\ x)]" >::
        (fun () ->
           let t = (3 /// db 3) in
           let t = hnorm t in
             assert_term_equal (3 /// db 3) t) ;

      "[(x\\ y\\ z\\ x) a]" >::
        (fun () ->
           let a = uconst "a" in
           let t = (3 /// db 3) ^^ [a] in
           let t = hnorm t in
             assert_term_equal (2 /// a) t) ;

      "[(x\\ x (x\\ x)) (x\\y\\ x y)]" >::
        (fun () ->
           let t = 1 /// (db 1 ^^ [1 /// db 1]) in
           let t = t ^^ [ 2 /// (db 2 ^^ [db 1]) ] in
           let t = hnorm t in
             assert_term_equal (1 /// ((1 /// db 1) ^^ [db 1]))  t) ;

      "[(x\\ x (x\\ x)) (x\\y\\ x y) c]" >::
        (fun () ->
           let c = uconst "c" in
           let t = 1 /// (db 1 ^^ [1 /// db 1]) in
           let t = t ^^ [ 2 /// (db 2 ^^ [db 1]) ; c ] in
           let t = hnorm t in
             assert_term_equal c t) ;

      "[x\\ c x]" >::
        (fun () ->
           let c = uconst "c" in
           let t = 1 /// (c ^^ [db 1]) in
           let t = hnorm t in
             assert_term_equal (1 /// (c ^^ [db 1])) t) ;

      (* This is a normalization pb which appeared to be causing
       * a failure in an unification test below. *)
      "[x\\y\\((a\\b\\ a b) x y)]" >::
        (fun () ->
           let ii = 2 /// (db 2 ^^ [db 1]) in
           let t = 2 /// (ii ^^ [db 2;db 1]) in
           let t = hnorm t in
             assert_term_equal (2///(db 2 ^^ [db 1])) t) ;

      (* Test that Term.App is flattened *)
      "[(a b) c]" >::
        (fun () ->
           let a = uconst "a" in
           let b = uconst "b" in
           let c = uconst "c" in
           let t = (a ^^ [b]) ^^ [c] in
           let t = hnorm t in
             assert_term_equal (a ^^ [b ; c]) t) ;

      (* Test that Term.Lam is flattened *)
      "[x\\ (y\\ x)]" >::
        (fun () ->
           let t = 1 /// (1 /// db 2) in
           let t = hnorm t in
             assert_term_equal (2 /// db 2) t) ;
    ]

let pprint_tests =
  "Pprint" >:::
    [
      "eval P V" >::
        (fun () ->
           let p = uconst "P" in
           let v = uconst "V" in
           let t = app (uconst "eval") [p; v] in
             assert_term_pprint_equal "eval P V" t) ;

      "eval (abs R) (abs R)" >::
        (fun () ->
           let absR = (app (uconst "abs") [uconst "R"]) in
           let t = app (uconst "eval") [absR; absR] in
             assert_term_pprint_equal "eval (abs R) (abs R)" t) ;

      "A => B" >::
        (fun () ->
           let a = uconst "A" in
           let b = uconst "B" in
           let t = app (uconst "=>") [a; b] in
             assert_term_pprint_equal "A => B" t) ;

      "pi x\\eq x x" >::
        (fun () ->
           let t = app (uconst "pi") [1 /// (app (uconst "eq") [db 1; db 1])] in
             assert_term_pprint_equal "pi x1\\eq x1 x1" t) ;

      "pi x\\typeof x U => typeof (R x) T" >::
        (fun () ->
           let typeofxU = app (uconst "typeof") [db 1; uconst "U"] in
           let rx = app (uconst "R") [db 1] in
           let typeofRxT = app (uconst "typeof") [rx; uconst "T"] in
           let t = app (uconst "pi")
             [1 /// (app (uconst "=>") [typeofxU; typeofRxT])] in
             assert_term_pprint_equal
               "pi x1\\typeof x1 U => typeof (R x1) T" t) ;

      "pi (A B)" >::
        (fun () ->
           let t = app (uconst "pi") [app (uconst "A") [uconst "B"]] in
             assert_term_pprint_equal "pi (A B)" t) ;

      "pi x\\A :: L" >::
        (fun () ->
           let t = app (uconst "::")
             [app (uconst "pi") [1 /// uconst "A"] ;
                   uconst "L"] in
             assert_term_pprint_equal "(pi x1\\A) :: L" t) ;

      "p (x\\A)" >::
        (fun () ->
           let t = app (uconst "p") [1 /// uconst "A"] in
             assert_term_pprint_equal "p (x1\\A)" t) ;
    ]

let typing_tests =
  "Typing" >:::
    [
      "F:(a->b->c) A:a B:b" >::
        (fun () ->
           let f = const "F" (tyarrow [aty; bty] cty) in
           let a = const "A" aty in
           let b = const "B" bty in
             assert_ty_equal cty (tc [] (f ^^ [a; b]))) ;

      "x:a\\y:b\\x" >::
        (fun () ->
           assert_ty_equal
             (tyarrow [aty; bty] aty)
             (tc [] ([bty; aty] // db 2))) ;
    ]

let binding_tests =
  "Binding" >:::
    [
      "Should not bind variable to itself" >::
        (fun () ->
           let v1 = uvar Logic "v1" 0 in
             assert_raises_any
               (fun () -> bind v1 v1)) ;

      "Should not bind variable to itself (2)" >::
        (fun () ->
           let v1 = uvar Logic "v1" 0 in
           let v2 = uvar Logic "v2" 0 in
             bind v1 v2 ;
             assert_raises_any
               (fun () -> bind v2 v1)) ;
    ]

let tests =
  "Term" >::: [norm_tests; pprint_tests; typing_tests; binding_tests]
