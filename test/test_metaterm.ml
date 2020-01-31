open OUnit
open Test_helper
open Term
open Term.Notations
open Metaterm

let var_a = uvar Eigen "A" 0
let var_b = uvar Eigen "B" 0
let var_c = uvar Eigen "C" 0

let a = termobj var_a
let b = termobj var_b
let c = termobj var_c

let assert_raises_unify_failure f =
  try
    f () ;
    assert_failure "Expected UnifyFailure"
  with
    | Unify.UnifyFailure _ -> ()

let assert_metaterm_unify s1 s2 =
  let ctx = List.map (fun id -> (id, var Logic id 0 ity)) ["?1"; "?2"; "?3"] in
  let t1 = parse_metaterm ~ctx s1 in
  let t2 = parse_metaterm ~ctx s2 in
    meta_right_unify t1 t2 ;
    assert_metaterm_equal t1 t2

let tests =
  "Metaterm" >:::
    [
      "Print equality" >::
        (fun () ->
           let t = Eq(var_a, var_b) in
             assert_pprint_equal "A = B" t) ;

      "Print object" >::
        (fun () ->
           let eval = uconst "eval" in
           let t = termobj (eval ^^ [var_a; var_b]) in
             assert_pprint_equal "{eval A B}" t) ;

      "Print arrow" >::
        (fun () ->
           let t = arrow a b  in
             assert_pprint_equal "{A} -> {B}" t) ;

      "Print multiple arrows" >::
        (fun () ->
           let t = arrow a (arrow b c)  in
             assert_pprint_equal "{A} -> {B} -> {C}" t) ;

      "Print forall" >::
        (fun () ->
           let t = forall [("A", emptyty)] b in
             assert_pprint_equal "forall A, {B}" t) ;

      "Print exists" >::
        (fun () ->
           let t = exists [("A", emptyty)] b in
             assert_pprint_equal "exists A, {B}" t) ;

      "Print smaller restricted object" >::
        (fun () ->
           let t = set_restriction (Smaller 1) a in
             assert_pprint_equal "{A}*" t) ;

      "Print equal restricted object" >::
        (fun () ->
           let t = set_restriction (Equal 1) a in
             assert_pprint_equal "{A}@" t) ;

      "Print co-smaller restricted object" >::
        (fun () ->
           let t = set_restriction (CoSmaller 1) a in
             assert_pprint_equal "{A}+" t) ;

      "Print co-equal restricted object" >::
        (fun () ->
           let t = set_restriction (CoEqual 1) a in
             assert_pprint_equal "{A}#" t) ;

      "Print second smaller restricted object" >::
        (fun () ->
           let t = set_restriction (Smaller 2) a in
             assert_pprint_equal "{A}**" t) ;

      "Print OR" >::
        (fun () ->
           let t = meta_or a b in
             assert_pprint_equal "{A} \\/ {B}" t) ;

      "Print AND" >::
        (fun () ->
           let t = meta_and a b in
             assert_pprint_equal "{A} /\\ {B}" t) ;

      "Print multiple \\/" >::
        (fun () ->
           let t = meta_or (meta_or a b) c in
             assert_pprint_equal "{A} \\/ {B} \\/ {C}" t) ;

      "Print multiple OR (right assoc)" >::
        (fun () ->
           let t = meta_or a (meta_or b c) in
             assert_pprint_equal "{A} \\/ ({B} \\/ {C})" t) ;

      "Print OR within arrow" >::
        (fun () ->
           let t = arrow a (meta_or b c) in
             assert_pprint_equal "{A} -> {B} \\/ {C}" t) ;

      "Print arrow within OR" >::
        (fun () ->
           let t = meta_or (arrow a b) c in
             assert_pprint_equal "({A} -> {B}) \\/ {C}" t) ;

      "Print OR within AND" >::
        (fun () ->
           let t = meta_and a (meta_or b c) in
             assert_pprint_equal "{A} /\\ ({B} \\/ {C})" t) ;

      "Print AND within OR" >::
        (fun () ->
           let t = meta_or a (meta_and b c) in
             assert_pprint_equal "{A} \\/ {B} /\\ {C}" t) ;

      "Print exists left of OR" >::
        (fun () ->
           let t = meta_or (exists [("A", emptyty)] b) c in
             assert_pprint_equal "(exists A, {B}) \\/ {C}" t) ;

      "Replace should descend underneath exists" >::
        (fun () ->
           let t = exists [("A", emptyty)] b in
           let t' = replace_metaterm_vars [("B", var_c)] t in
             assert_pprint_equal "exists A, {C}" t') ;

      "Replace should not descend underneath exists if names are equal" >::
        (fun () ->
           let t = exists [("A", emptyty)] a in
           let t' = replace_metaterm_vars [("A", var_b)] t in
             assert_pprint_equal "exists A, {A}" t') ;

      "Replace should not capture exists variables" >::
        (fun () ->
           let t = exists [("A", emptyty)] b in
           let t' = replace_metaterm_vars [("B", var_a)] t in
             assert_pprint_equal "exists A1, {A}" t') ;

      "Cascading capture" >::
        (fun () ->
           let t = forall [("E2", emptyty)]
             (arrow (Eq(uconst "E2", uvar Eigen "E" 0))
                (exists [("E1", emptyty)] (Eq(uconst "E1", uconst "E2")))) in
           let t' = replace_metaterm_vars [("E", uvar Eigen "E1" 0)] t in
             assert_pprint_equal
               "forall E2, E2 = E1 -> (exists E3, E3 = E2)" t');

      "Print non-empty context" >::
        (fun () ->
           let context = Context.add (uconst "L") Context.empty in
           let t = Obj ({context ; right = var_a ; mode = Async}, Irrelevant) in
             assert_pprint_equal "{L |- A}" t) ;

      "Print predicate" >::
        (fun () ->
           let p = uconst "head" ^^ [var_a; var_b] in
           let t = Pred(p, Irrelevant) in
             assert_pprint_equal "head A B" t) ;

      "Print restricted predicate" >::
        (fun () ->
           let p = uconst "head" ^^ [var_a; var_b] in
           let t = Pred(p, Smaller 1) in
             assert_pprint_equal "head A B *" t) ;

      "Print object quantifier inside of predicate" >::
        (fun () ->
           let t = pred (uconst "prove" ^^
                           [uconst "pi" ^^ [uconst "G"]]) in
             assert_pprint_equal "prove (pi G)" t) ;

      "Normalize should move all implications to the context" >::
        (fun () ->
           let context = Context.add (uconst "L") Context.empty in
           let bc = uconst "=>" ^^ [uconst "B"; uconst "C"] in
           let right = uconst "=>" ^^ [uconst "A"; bc] in
           let t = Obj ({context ; right ; mode = Async}, Irrelevant) in
           assert_pprint_equal "{L |- A => B => C}" t ;
           assert_pprint_equal "{L, A, B |- C}" (normalize t)) ;

      "Normalize should instantiate pi x\\ with nominal constant" >::
        (fun () ->
           let pi = const "pi" iiity in
           let pred = const "pred" iiity in
           let t = pi ^^ [[("x",ity)] // (pred ^^ [db 1; db 1])] in
           let t = termobj t in
             assert_pprint_equal "{pi x1\\pred x1 x1}" t ;
             assert_pprint_equal "{pred n1 n1}" (normalize t)) ;

      "Normalize should rename bound variables if needed" >::
        (fun () ->
           let const_a = uconst "A" in
           let p = uconst "p" in
           let t = forall [("A", emptyty)]
             (arrow (pred (p ^^ [var_a])) (pred (p ^^ [const_a])))
           in
             assert_pprint_equal "forall A1, p A -> p A1" (normalize t)) ;

      "Normalize should rename bound nabla variables if needed" >::
        (fun () ->
           let const_n1 = uconst "n1" in
           let nom_n1 = nominal_var "n1" emptyty in
           let p = uconst "p" in
           let t = forall [("n1", emptyty)]
             (arrow (pred (p ^^ [nom_n1])) (pred (p ^^ [const_n1])))
           in
             assert_pprint_equal "forall n2, p n1 -> p n2" (normalize t)) ;

      "Normalize should rename nested binders" >::
        (fun () ->
           (* The var_a should force renaming of the A which should
              cascade and force renaming of A1 *)
           let eq = Eq(uconst "A", uconst "A1") in
           let t = Binding(Forall, [("A", emptyty)],
                           Arrow(pred var_a,
                                 Binding(Forall, [("A1", emptyty)], eq)))
           in
             assert_pprint_equal "forall A1, A -> (forall A2, A1 = A2)"
               (normalize t) );

      "Normalize should rename nested binders (2)" >::
        (fun () ->
           let eq = Eq(uconst "A1", uconst "A1") in
           let t = Binding(Forall, [("A1", emptyty)],
                           Arrow(Eq(var_a, uvar Eigen "A1" 0),
                                 Binding(Forall, [("A1", emptyty)], eq)))
           in
             assert_pprint_equal "forall A2, A = A1 -> (forall A3, A3 = A3)"
               (normalize t) );

      "Normalize should rename nominals of different types" >::
        (fun () ->
           let t = pred ((uconst "foo") ^^ [nominal_var "n1" aty;
                                            nominal_var "n1" bty;
                                            nominal_var "n2" aty])
           in
             assert_pprint_equal "foo n3 n1 n2" (normalize t)) ;

      "Meta right unify - equality" >::
        (fun () ->
           assert_metaterm_unify
             "t1 = t2"
             "?1 = ?2") ;

      "Meta right unify - pred" >::
        (fun () ->
           assert_metaterm_unify
             "foo t1"
             "foo ?1") ;

      "Meta right unify - arrow" >::
        (fun () ->
           assert_metaterm_unify
             "foo t1 -> bar t2"
             "foo ?1 -> bar ?2") ;

      "Meta right unify - forall" >::
        (fun () ->
           assert_metaterm_unify
             "forall A, rel1 t1 A"
             "forall A, rel1 ?1 A") ;

      "Meta right unify - obj" >::
        (fun () ->
           assert_metaterm_unify
             "{p2 t2 |- p1 t1}"
             "{p2 t2 |- p1 ?1}") ;

      "Meta right unify - variable capture" >::
        (fun () ->
           assert_raises_unify_failure
             (fun () ->
                assert_metaterm_unify
                  "forall A, rel1 A A"
                  "forall A, rel1 A ?1")) ;

      "Meta right unify - variable renaming" >::
        (fun () ->
           let t1 = parse_metaterm "forall A, foo A" in
           let t2 = parse_metaterm "forall B, foo B" in
             meta_right_unify t1 t2) ;

      "Meta right unify - variable renaming (2)" >::
        (fun () ->
           let ctx = [("?1", var Logic "?1" 0 (tyarrow [iity] ity))] in
           let t1 = parse_metaterm ~ctx "forall A, foo (iabs A)" in
           let t2 = parse_metaterm ~ctx "forall B, foo (?1 B)" in
             meta_right_unify t1 t2 ;
             assert_pprint_equal "forall B, foo (iabs B)" t2) ;

      "Fresh raised alist with subordination" >::
        (fun () ->
           let tm = tybase (atybase "tm") in
           let tp = tybase (atybase "tp") in
           let t_lam = tyarrow [tp; tyarrow [tm] tm] tm in
           let sr = Subordination.update Subordination.empty t_lam in
           let sr = Subordination.close sr [atybase "tp"; atybase "tm"] in
           let support = [nominal_var "n1" tm; nominal_var "n2" tp] in
           let tids = [("X", tm); ("Y", tp)] in
             match
               fresh_raised_alist ~used:[] ~sr ~tag:Eigen ~support tids
             with
               | ([(_, rx); (_, ry)], [x'; y']) ->
                   assert_term_pprint_equal ((term_to_string x') ^ " n1 n2") rx ;
                   assert_term_pprint_equal ((term_to_string y') ^ " n2") ry ;
               | _ -> assert false
        ) ;

    ]
