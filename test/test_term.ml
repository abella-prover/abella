open Abella_lib
open Term
open Term.Notations
open Test_helper

let norm_tests = [
      test_case "[(x\\ x) c]"
        (fun () ->
           let c = uconst "c" in
           let t = (1 /// db 1) ^^ [c] in
           let t = hnorm t in
             Alcotest.check term_testable "terms differ" c t) ;

      test_case "[(x\\ y\\ x) a b]"
        (fun () ->
           let a = uconst "a" in
           let b = uconst "b" in
           let t = (2 /// db 2) ^^ [a; b] in
           let t = hnorm t in
             Alcotest.check term_testable "terms differ" a t) ;

      test_case "[(x\\ y\\ y) a b]"
        (fun () ->
           let a = uconst "a" in
           let b = uconst "b" in
           let t = (2 /// db 1) ^^ [a; b] in
           let t = hnorm t in
             Alcotest.check term_testable "terms differ" b t) ;

      test_case "[(x\\ y\\ z\\ x)]"
        (fun () ->
           let t = (3 /// db 3) in
           let t = hnorm t in
             Alcotest.check term_testable "terms differ" (3 /// db 3) t) ;

      test_case "[(x\\ y\\ z\\ x) a]"
        (fun () ->
           let a = uconst "a" in
           let t = (3 /// db 3) ^^ [a] in
           let t = hnorm t in
             Alcotest.check term_testable "terms differ" (2 /// a) t) ;

      test_case "[(x\\ x (x\\ x)) (x\\y\\ x y)]"
        (fun () ->
           let t = 1 /// (db 1 ^^ [1 /// db 1]) in
           let t = t ^^ [ 2 /// (db 2 ^^ [db 1]) ] in
           let t = hnorm t in
             Alcotest.check term_testable "terms differ" (1 /// ((1 /// db 1) ^^ [db 1]))  t) ;
      test_case "[(x\\ x (x\\ x)) (x\\y\\ x y) c]"
        (fun () ->
           let c = uconst "c" in
           let t = 1 /// (db 1 ^^ [1 /// db 1]) in
           let t = t ^^ [ 2 /// (db 2 ^^ [db 1]) ; c ] in
           let t = hnorm t in
             Alcotest.check term_testable "terms differ" c t) ;

      test_case "[x\\ c x]"
        (fun () ->
           let c = uconst "c" in
           let t = 1 /// (c ^^ [db 1]) in
           let t = hnorm t in
             Alcotest.check term_testable "terms differ" (1 /// (c ^^ [db 1])) t) ;

      (* This is a normalization pb which appeared to be causing
       * a failure in an unification test below. *)
      test_case "[x\\y\\((a\\b\\ a b) x y)]"
        (fun () ->
           let ii = 2 /// (db 2 ^^ [db 1]) in
           let t = 2 /// (ii ^^ [db 2;db 1]) in
           let t = hnorm t in
             Alcotest.check term_testable "terms differ" (2///(db 2 ^^ [db 1])) t) ;

      (* Test that Term.App is flattened *)
      test_case "[(a b) c]"
        (fun () ->
           let a = uconst "a" in
           let b = uconst "b" in
           let c = uconst "c" in
           let t = (a ^^ [b]) ^^ [c] in
           let t = hnorm t in
             Alcotest.check term_testable "terms differ" (a ^^ [b ; c]) t) ;

      (* Test that Term.Lam is flattened *)
      test_case "[x\\ (y\\ x)]"
        (fun () ->
           let t = 1 /// (1 /// db 2) in
           let t = hnorm t in
             Alcotest.check term_testable "terms differ" (2 /// db 2) t) ;
    ]

let pprint_tests = [
      test_case "eval P V"
        (fun () ->
           let p = uconst "P" in
           let v = uconst "V" in
           let t = app (uconst "eval") [p; v] in
             assert_term_pprint_equal "eval P V" t) ;

      test_case "eval (abs R) (abs R)"
        (fun () ->
           let absR = (app (uconst "abs") [uconst "R"]) in
           let t = app (uconst "eval") [absR; absR] in
             assert_term_pprint_equal "eval (abs R) (abs R)" t) ;

      test_case "A => B"
        (fun () ->
           let a = uconst "A" in
           let b = uconst "B" in
           let t = app (uconst "=>") [a; b] in
             assert_term_pprint_equal "A => B" t) ;

      test_case "pi x\\eq x x"
        (fun () ->
           let t = app (uconst "pi") [1 /// (app (uconst "eq") [db 1; db 1])] in
             assert_term_pprint_equal "pi x1\\eq x1 x1" t) ;

      test_case "pi x\\typeof x U => typeof (R x) T"
        (fun () ->
           let typeofxU = app (uconst "typeof") [db 1; uconst "U"] in
           let rx = app (uconst "R") [db 1] in
           let typeofRxT = app (uconst "typeof") [rx; uconst "T"] in
           let t = app (uconst "pi")
             [1 /// (app (uconst "=>") [typeofxU; typeofRxT])] in
             assert_term_pprint_equal
               "pi x1\\typeof x1 U => typeof (R x1) T" t) ;

      test_case "pi (A B)"
        (fun () ->
           let t = app (uconst "pi") [app (uconst "A") [uconst "B"]] in
             assert_term_pprint_equal "pi (A B)" t) ;

      test_case "((pi x\\p x) => qx) != (pi x\\(p x => q x))"
        (fun () ->
          let p = const "p" (tyarrow [tybase (atybase "x")] oty) in
          let q = const "q" (tyarrow [tybase (atybase "x")] oty) in
          let mkpi x ty f =
            app (const "pi" (tyarrow [tyarrow [ty] oty] oty)) [lambda [x, ty] f] in
          let mkimp f g =
            app (const "=>" (tyarrow [oty ; oty] oty)) [f ; g] in
          let ity = tybase (atybase "i") in
          let t1 =
            mkpi "x" ity (mkimp (app p [db 1]) (app q [db 1])) |> term_to_string in
          let t2 =
            mkimp (mkpi "x" ity (app p [db 1])) (app q [db 1]) |> term_to_string in
          Alcotest.check Alcotest.bool
            (t1 ^ " == " ^ t2) true (t1 <> t2)) ;
    ]

let typing_tests = [
      test_case "F:(a->b->c) A:a B:b"
        (fun () ->
           let f = const "F" (tyarrow [aty; bty] cty) in
           let a = const "A" aty in
           let b = const "B" bty in
             Alcotest.check ty_testable "types differ" cty (tc [] (f ^^ [a; b]))) ;

      test_case "x:a\\y:b\\x"
        (fun () ->
           Alcotest.check ty_testable "types differ"
             (tyarrow [aty; bty] aty)
             (tc [] ([("x",aty); ("y",bty)] // db 2))) ;
    ]

let binding_tests = [
      test_case "Should not bind variable to itself"
        (fun () ->
           let v1 = uvar Logic "v1" 0 in
             Alcotest.match_raises "expected exception" (fun _ -> true)
               (fun () -> ignore (bind v1 v1))) ;

      test_case "Should not bind variable to itself (2)"
        (fun () ->
           let v1 = uvar Logic "v1" 0 in
           let v2 = uvar Logic "v2" 0 in
             bind v1 v2 ;
             Alcotest.match_raises "expected exception" (fun _ -> true)
               (fun () -> ignore (bind v2 v1))) ;
    ]

let abstract_tests = [
      test_case "Should not capture unprotected dB's (single layer)"
        (fun () ->
          let g = uconst "g" in
          let h = uconst "h" in
          let x = uconst "X" in
          (*    `1 (g (y\ h `1 X)) *)
          let t = db 1 ^^ [(g ^^ [1 /// (h ^^ [db 1; x])])] in
          let actual = abstract "X" emptyty t in
          (* x\ `2 (g (y\ h y  x)) *)
          let expected = 1 /// (db 2 ^^ [(g ^^ [1 /// (h ^^ [db 1; db 2])])]) in
          Alcotest.check term_testable "terms differ" expected actual) ;

      test_case "Should not capture unprotected dB's (multilayer)"
        (fun () ->
          let x = uconst "X" in
          let y = uconst "Y" in
          let z = uconst "Z" in
          (*       X `1 (w\ Y w) Z *)
          let t = x ^^ [db 1; (1 /// (y ^^ [db 1])); z] in
          let actual = abstract "Y" emptyty (abstract "Z" emptyty t) in
          (* y\ z\ X `3 (w\ y w) z *)
          let expected = 2 /// (x ^^ [db 3; (1 /// (db 3 ^^ [db 1])); db 1]) in
          Alcotest.check term_testable "terms differ" expected actual) ;
    ]

let tests =
  suite "Term"
    (group "Norm" norm_tests @
     group "Pprint" pprint_tests @
     group "Typing" typing_tests @
     group "Binding" binding_tests @
     group "Abstract" abstract_tests)
