open OUnit
open Term
open Term.Notations
open Test_helper

let norm_tests =
  "Norm" >:::
    [
      "[(x\\ x) c]" >::
        (fun () ->
           let c = const ~ts:1 "c" in
           let t = (1 // db 1) ^^ [c] in
           let t = hnorm t in
             assert_term_equal c t) ;

      "[(x\\ y\\ x) a b]" >::
        (fun () ->
           let a = const ~ts:1 "a" in
           let b = const ~ts:1 "b" in
           let t = (2 // db 2) ^^ [a; b] in
           let t = hnorm t in
             assert_term_equal a t) ;

      "[(x\\ y\\ y) a b]" >::
        (fun () ->
           let a = const ~ts:1 "a" in
           let b = const ~ts:1 "b" in
           let t = (2 // db 1) ^^ [a; b] in
           let t = hnorm t in
             assert_term_equal b t) ;

      "[(x\\ y\\ z\\ x)]" >::
        (fun () ->
           let t = (3 // db 3) in
           let t = hnorm t in
             assert_term_equal (3 // db 3) t) ;

      "[(x\\ y\\ z\\ x) a]" >::
        (fun () ->
           let a = const ~ts:1 "a" in
           let t = (3 // db 3) ^^ [a] in
           let t = hnorm t in
             assert_term_equal (2 // a) t) ;

      "[(x\\ x (x\\ x)) (x\\y\\ x y)]" >::
        (fun () ->
           let t = 1 // (db 1 ^^ [1 // db 1]) in
           let t = t ^^ [ 2 // (db 2 ^^ [db 1]) ] in
           let t = hnorm t in
             assert_term_equal (1 // ((1 // db 1) ^^ [db 1]))  t) ;

      "[(x\\ x (x\\ x)) (x\\y\\ x y) c]" >::
        (fun () ->
           let c = const ~ts:1 "c" in
           let t = 1 // (db 1 ^^ [1 // db 1]) in
           let t = t ^^ [ 2 // (db 2 ^^ [db 1]) ; c ] in
           let t = hnorm t in
             assert_term_equal c t) ;

      "[x\\ c x]" >::
        (fun () ->
           let c = const ~ts:1 "c" in
           let t = 1 // (c ^^ [db 1]) in
           let t = hnorm t in
             assert_term_equal (1 // (c ^^ [db 1])) t) ;

      (* This is a normalization pb which appeared to be causing
       * a failure in an unification test below. *)
      "[x\\y\\((a\\b\\ a b) x y)]" >::
        (fun () ->
           let ii = 2 // (db 2 ^^ [db 1]) in
           let t = 2 // (ii ^^ [db 2;db 1]) in
           let t = hnorm t in
             assert_term_equal (2//(db 2 ^^ [db 1])) t) ;

      (* Test that Term.App is flattened *)
      "[(a b) c]" >::
        (fun () ->
           let a = const ~ts:1 "a" in
           let b = const ~ts:1 "b" in
           let c = const ~ts:1 "c" in
           let t = (a ^^ [b]) ^^ [c] in
           let t = hnorm t in
             assert_term_equal (a ^^ [b ; c]) t) ;

      (* Test that Term.Lam is flattened *)
      "[x\\ (y\\ x)]" >::
        (fun () ->
           let t = 1 // (1 // db 2) in
           let t = hnorm t in
             assert_term_equal (2 // db 2) t) ;
    ]

let pprint_tests =
  "Pprint" >:::
    [
      "eval P V" >::
        (fun () ->
           let p = const "P" in
           let v = const "V" in
           let t = app (const "eval") [p; v] in
             assert_term_pprint_equal "eval P V" t) ;

      "eval (abs R) (abs R)" >::
        (fun () ->
           let absR = (app (const "abs") [const "R"]) in
           let t = app (const "eval") [absR; absR] in
             assert_term_pprint_equal "eval (abs R) (abs R)" t) ;

      "A => B" >::
        (fun () ->
           let a = const "A" in
           let b = const "B" in
           let t = app (const "=>") [a; b] in
             assert_term_pprint_equal "A => B" t) ;

      "pi x\\eq x x" >::
        (fun () ->
           let t = app (const "pi") [1 // (app (const "eq") [db 1; db 1])] in
             assert_term_pprint_equal "pi x1\\eq x1 x1" t) ;

      "pi x\\typeof x U => typeof (R x) T" >::
        (fun () ->
           let typeofxU = app (const "typeof") [db 1; const "U"] in
           let rx = app (const "R") [db 1] in
           let typeofRxT = app (const "typeof") [rx; const "T"] in
           let t = app (const "pi")
             [1 // (app (const "=>") [typeofxU; typeofRxT])] in
             assert_term_pprint_equal
               "pi x1\\typeof x1 U => typeof (R x1) T" t) ;

      "pi (A B)" >::
        (fun () ->
           let t = app (const "pi") [app (const "A") [const "B"]] in
             assert_term_pprint_equal "pi (A B)" t) ;
    ]

let tests =
  "Term" >::: [norm_tests; pprint_tests]
