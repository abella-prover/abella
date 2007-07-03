open OUnit
open Test_helper
open Term
open Lppterm
open Tactics
  
let object_cut_tests =
  "Object Cut" >:::
    [
      "Simple" >::
        (fun () ->
           let t = object_cut (parse_obj "A |- B") (parse_obj "A") in
             assert_pprint_equal "{B}" t) ;
      
      "Compound" >::
        (fun () ->
           let h0 = parse_obj "eval A B |- typeof B C" in
           let h1 = parse_obj "eval A B" in
           let t = object_cut h0 h1 in
             assert_pprint_equal "{typeof B C}" t) ;

      "Contexts should be merged" >::
        (fun () ->
           let h0 = parse_obj "L1, A |- B" in
           let h1 = parse_obj "L2 |- A" in
           let t = object_cut h0 h1 in
             assert_pprint_equal "{L1, L2 |- B}" t) ;
    ]

let object_instantiation_tests =
  "Object Instantiation" >:::
    [
      "Simple" >::
        (fun () ->
           let n = nominal_var "n" in
           let obj = {context = Context.empty ;
                      term = app (const "eval") [n; const "B"]} in
           let a = var Eigen "A" 0 in
           let result = object_inst obj "n" a in
             assert_term_pprint_equal "eval A B" result.term) ;
    ]

let apply_tests =
  "Apply" >:::
    [
      "Normal" >::
        (fun () ->
           let h0 = freshen
             "forall A B C, {eval A B} -> {typeof A C} -> {typeof B C}" in
           let h1 = freshen "{eval (abs R) (abs R)}" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}" in
           let t, _ = apply h0 [Some h1; Some h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Properly restricted" >::
        (fun () ->
           let h0 = freshen
             "forall A B C, {eval A B}* -> {typeof A C} -> {typeof B C}" in
           let h1 = freshen "{eval (abs R) (abs R)}*" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}" in
           let t, _ = apply h0 [Some h1; Some h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Needlessly restricted" >::
        (fun () ->
           let h0 = freshen
             "forall A B C, {eval A B} -> {typeof A C} -> {typeof B C}" in
           let h1 = freshen "{eval (abs R) (abs R)}*" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}" in
           let t, _ = apply h0 [Some h1; Some h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;
      
      "Improperly restricted" >::
        (fun () ->
           let h0 = freshen
             "forall A B C, {eval A B}* -> {typeof A C} -> {typeof B C}" in
           let h1 = freshen "{eval (abs R) (abs R)}" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply h0 [Some h1; Some h2])) ;

      "Improperly restricted (2)" >::
        (fun () ->
           let h0 = freshen
             "forall A B C, {eval A B}* -> {typeof A C} -> {typeof B C}" in
           let h1 = freshen "{eval (abs R) (abs R)}@" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply h0 [Some h1; Some h2])) ;

      "Properly double restricted" >::
        (fun () ->
           let h0 = freshen
             "forall A B C, {eval A B}@ -> {typeof A C}** -> {typeof B C}" in
           let h1 = freshen "{eval (abs R) (abs R)}@" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}**" in
           let t, _ = apply h0 [Some h1; Some h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Improperly double restricted" >::
        (fun () ->
           let h0 = freshen
             "forall A B C, {eval A B}@ -> {typeof A C}** -> {typeof B C}" in
           let h1 = freshen "{eval (abs R) (abs R)}@" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}@@" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply h0 [Some h1; Some h2])) ;

      "Improperly double restricted (2)" >::
        (fun () ->
           let h0 = freshen
             "forall A B C, {eval A B}@ -> {typeof A C}** -> {typeof B C}" in
           let h1 = freshen "{eval (abs R) (abs R)}" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}**" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply h0 [Some h1; Some h2])) ;

      "Unification failure" >::
        (fun () ->
           let h0 = freshen
             "forall A B C, {eval A B} -> {typeof A C} -> {typeof B C}" in
           let h1 = freshen "{eval (abs R) (abs R)}" in
           let h2 = freshen "{bad (abs R) (arrow S T)}" in
           let clash = Unify.ConstClash (const "typeof", const "bad") in
             assert_raises (Unify.Failure clash)
               (fun () -> apply h0 [Some h1; Some h2])) ;

      "With contexts" >::
        (fun () ->
           let h0 = freshen
             ("forall E A C, {E, hyp A |- conc C} -> " ^
                "{E |- conc A} -> {E |- conc C}") in
           let h1 = freshen "{L, hyp A, hyp B1, hyp B2 |- conc C}" in
           let h2 = freshen "{L |- conc A}" in
           let t, _ = apply h0 [Some h1; Some h2] in
             assert_pprint_equal "{L, hyp B1, hyp B2 |- conc C}" t) ;

      "On non-object" >::
        (fun () ->
           let h0 = freshen "forall A, pred A -> result A" in
           let h1 = freshen "pred B" in
           let t, _ = apply h0 [Some h1] in
             assert_pprint_equal "result B" t) ;

      "Absent argument should produce corresponding obligation" >::
        (fun () ->
           let h0 = freshen
             ("forall L A, ctx L -> {L |- conc A} -> " ^
                "{L, hyp A |- pred} -> false") in
           let h1 = freshen "{L |- conc A}" in
           let h2 = freshen "{L, hyp A, hyp B, hyp C |- pred}" in
           let _, obligations = apply h0 [None; Some h1; Some h2] in
             match obligations with
               | [term] ->
                   assert_pprint_equal "ctx (hyp C :: hyp B :: L)" term
               | _ -> assert_failure
                   ("Expected one obligation but found " ^
                      (string_of_int (List.length obligations)))) ;

    ]

let assert_expected_cases n cases =
  assert_failure (Printf.sprintf "Expected %d case(s) but found %d case(s)"
                    n (List.length cases))

let case ?(used=[]) ?(clauses=[]) ?(meta_clauses=[]) term =
  case ~used ~clauses ~meta_clauses term
    
let case_tests =
  "Case" >:::
    [
      "Normal" >::
        (fun () ->
           let term = freshen "{eval A B}" in
           let used = ["A"; "B"] in
             match case ~used ~clauses:eval_clauses term with
               | [case1; case2] ->
                   set_bind_state case1.bind_state ;
                   assert_pprint_equal "{eval (abs R) (abs R)}" term ;
                   assert_bool "R should be flagged as used"
                     (List.mem "R" (List.map fst case1.new_vars)) ;
                   
                   set_bind_state case2.bind_state ;
                   assert_pprint_equal "{eval (app M N) B}" term ;
                   begin match case2.new_hyps with
                     | [h1; h2] ->
                         assert_pprint_equal "{eval M (abs R)}" h1 ;
                         assert_pprint_equal "{eval (R N) B}" h2 ;
                     | _ -> assert_failure "Expected 2 new hypotheses"
                   end ;
                   assert_bool "R should be flagged as used"
                     (List.mem "R" (List.map fst case2.new_vars)) ;
                   assert_bool "M should be flagged as used"
                     (List.mem "M" (List.map fst case2.new_vars)) ;
                   assert_bool "N should be flagged as used"
                     (List.mem "N" (List.map fst case2.new_vars))
               | cases -> assert_expected_cases 2 cases) ;
      
      "Restriction should become smaller" >::
        (fun () ->
           let term = freshen "{foo A}@" in
           let clauses = parse_clauses "foo X :- bar X." in
           let used = ["A"] in
             match case ~used ~clauses term with
               | [case1] ->
                   set_bind_state case1.bind_state ;
                   begin match case1.new_hyps with
                     | [hyp] ->
                         assert_pprint_equal "{bar A}*" hyp ;
                     | _ -> assert_failure "Expected 1 new hypothesis"
                   end
               | cases -> assert_expected_cases 1 cases) ;

      "On OR" >::
        (fun () ->
           let term = freshen "{A} \\/ {B}" in
           let used = ["A"; "B"] in
             match case ~used term with
               | [{new_hyps=[hyp1]} ; {new_hyps=[hyp2]}] ->
                   assert_pprint_equal "{A}" hyp1 ;
                   assert_pprint_equal "{B}" hyp2 ;
               | _ -> assert_failure "Pattern mismatch") ;

      "On exists" >::
        (fun () ->
           let term = freshen "exists A B, {foo A B}" in
           let used = [] in
             match case ~used term with
               | [{new_vars=new_vars ; new_hyps=[hyp]}] ->
                   let var_names = List.map fst new_vars in
                     assert_string_list_equal ["A"; "B"] var_names ;
                     assert_pprint_equal "{foo A B}" hyp ;
               | _ -> assert_failure "Pattern mismatch") ;

      "On implies" >::
        (fun () ->
           let term = freshen "{L |- hyp A => conc B}" in
           let used = [] in
             match case ~used term with
               | [{new_vars=[] ; new_hyps=[hyp]}] ->
                   assert_pprint_equal "{L, hyp A |- conc B}" hyp
               | _ -> assert_failure "Pattern mismatch") ;

      "Should look in context for member" >::
        (fun () ->
           let term = freshen "{L, hyp A |- hyp B}" in
           let used = ["L"; "A"; "B"] in
             match case ~used term with
               | [{new_vars=[] ; new_hyps=[hyp]}] ->
                   assert_pprint_equal "member (hyp B) (hyp A :: L)" hyp
               | _ -> assert_failure "Pattern mismatch") ;

      "Should pass along context" >::
        (fun () ->
           let term = freshen "{L |- foo A}" in
           let clauses = parse_clauses "foo X :- bar X." in
           let used = ["A"] in
             match case ~used ~clauses term with
               | [case1; case2] ->
                   (* case1 is the member case *)
                   
                   set_bind_state case2.bind_state ;
                   begin match case2.new_hyps with
                     | [hyp] ->
                         assert_pprint_equal "{L |- bar A}" hyp ;
                     | _ -> assert_failure "Expected 1 new hypothesis"
                   end ;
               | cases -> assert_expected_cases 3 cases) ;

      "On member" >::
        (fun () ->
           let term = freshen "member (hyp A) (hyp C :: L)" in
           let used = ["A"; "C"; "L"] in
           let meta_clauses =
             parse_clauses ("member A (A :: L)." ^
                              "member A (B :: L) :- member A L.")
           in
             match case ~used ~meta_clauses term with
               | [case1; case2] ->
                   set_bind_state case1.bind_state ;
                   assert_pprint_equal "member (hyp C) (hyp C :: L)" term ;

                   set_bind_state case2.bind_state ;
                   begin match case2.new_hyps with
                     | [hyp] ->
                         assert_pprint_equal "member (hyp A) L" hyp ;
                     | _ -> assert_failure "Expected 1 new hypothesis"
                   end
               | cases -> assert_expected_cases 2 cases) ;

      "Should raise over nominal variables in meta clauses" >::
        (fun () ->
           let meta_clauses = parse_clauses "pred M N." in
           let term = make_nominals ["n"] (freshen "pred (A n) B") in
           let used = ["A"; "B"] in
             match case ~used ~meta_clauses term with
               | [case1] -> ()
               | cases -> assert_expected_cases 1 cases) ;
             
      "Should raise over nominal variables in clauses" >::
        (fun () ->
           let clauses = parse_clauses "pred M N." in
           let term = make_nominals ["n"] (freshen "{pred (A n) B}") in
           let used = ["A"; "B"] in
             match case ~used ~clauses term with
               | [case1] -> ()
               | cases -> assert_expected_cases 1 cases) ;
             
    ]

let induction_tests =
  "Induction" >:::
    [
      "Single" >::
        (fun () ->
           let stmt = freshen
               "forall A, {first A} -> {second A} -> {third A}" in
           let (ih, goal) = induction 1 stmt in
             assert_pprint_equal
               "forall A, {first A}* -> {second A} -> {third A}"
               ih ;
             assert_pprint_equal
               "forall A, {first A}@ -> {second A} -> {third A}"
               goal) ;
      
      "Nested" >::
        (fun () ->
           let stmt = freshen
               "forall A, {first A} -> {second A} -> {third A}" in
           let (ih, goal) = induction 1 stmt in
             assert_pprint_equal
               "forall A, {first A}* -> {second A} -> {third A}" ih ;
             assert_pprint_equal
               "forall A, {first A}@ -> {second A} -> {third A}" goal ;
             let (ih, goal) = induction 2 goal in
               assert_pprint_equal
                 "forall A, {first A}@ -> {second A}** -> {third A}" ih ;
               assert_pprint_equal
                 "forall A, {first A}@ -> {second A}@@ -> {third A}" goal) ;
      
      "With OR on left of arrow" >::
        (fun () ->
           let stmt = freshen "forall X, {A} \\/ {B} -> {C} -> {D}" in
           let (ih, goal) = induction 2 stmt in
             assert_pprint_equal
               "forall X, {A} \\/ {B} -> {C}* -> {D}"
               ih ;
             assert_pprint_equal
               "forall X, {A} \\/ {B} -> {C}@ -> {D}"
               goal) ;
    ]

let assert_search_success b = assert_bool "Search should succeed" b
let assert_search_failure b = assert_bool "Search should fail" (not b)

let search ?(depth=5) ?(hyps=[]) ?(clauses=[]) ?(meta_clauses=[]) goal =
  search ~depth ~hyps ~clauses ~meta_clauses goal
    
let search_tests =
  "Search" >:::
    [
      "Should check hypotheses" >::
        (fun () ->
           let goal = freshen "{eval A B}" in
             assert_search_success (search ~depth:0 ~hyps:[goal] goal)) ;
      
      "Should should succeed if clause matches" >::
        (fun () ->
           let goal = freshen "{eval (abs R) (abs R)}" in
             assert_search_success
               (search ~depth:1 ~clauses:eval_clauses goal)) ;
      
      "Should backchain on clauses" >::
        (fun () ->
           let goal = freshen "{foo A}" in
           let clauses = parse_clauses "foo X :- bar X, baz X." in
           let hyps = [freshen "{bar A}"; freshen "{baz A}"] in
             assert_search_success
               (search ~clauses ~hyps goal)) ;

      "On left of OR" >::
        (fun () ->
           let hyp = freshen "{eval A B}" in
           let goal = freshen "{eval A B} \\/ {false}" in
             assert_search_success (search ~hyps:[hyp] goal)) ;
      
      "On right of OR" >::
        (fun () ->
           let hyp = freshen "{eval A B}" in
           let goal = freshen "{false} \\/ {eval A B}" in
             assert_search_success (search ~hyps:[hyp] goal)) ;

      "On exists" >::
        (fun () ->
           let goal = freshen "exists R, {eq (app M N) R}" in
           let clauses = parse_clauses "eq X X." in
             assert_search_success (search ~clauses goal)) ;

      "Should fail if there is no proof" >::
        (fun () ->
           let goal = freshen "{eval A B}" in
             assert_search_failure
               (search ~depth:5 ~clauses:eval_clauses goal)) ;
      
      "Should check context" >::
        (fun () ->
           let goal = freshen "{eval A B |- eval A B}" in
             assert_search_success (search ~depth:0 goal)) ;

      "Should fail if hypothesis has non-subcontext" >::
        (fun () ->
           let hyp = freshen "{eval A B |- eval A B}" in
           let goal = freshen "{eval A B}" in
             assert_search_failure
               (search ~depth:5 ~hyps:[hyp] goal)) ;

      "Should preserve context while backchaining" >::
        (fun () ->
           let goal = freshen
             "{eval M (abs R), eval (R N) V |- eval (app M N) V}"
           in
             assert_search_success (search ~clauses:eval_clauses goal)) ;

      "Should move implies to the left" >::
        (fun () ->
           let hyp = freshen "{A |- B}" in
           let goal = freshen "{A => B}" in
             assert_search_success (search ~hyps:[hyp] goal)) ;

      "Should replace pi x\\ with nominal variable" >::
        (fun () ->
           let hyp = make_nominals ["n1"] (freshen "{pred n1 n1}") in
           let goal = freshen "{pi x\\ pred x x}" in
             assert_search_success (search ~hyps:[hyp] goal)) ;

      "Should look for member" >::
        (fun () ->
           let hyp = freshen "member (hyp A) L" in
           let goal = freshen "{L |- hyp A}" in
             assert_search_success (search ~hyps:[hyp] goal)) ;

      "Should backchain on meta-clauses" >::
        (fun () ->
           let meta_clauses =
             parse_clauses
               ("member A (A :: L)." ^
                  "member A (B :: L) :- member A L.")
           in
           let hyp = freshen "member E K" in
           let goal = freshen "member E (F :: K)" in
             assert_search_success (search ~hyps:[hyp] ~meta_clauses goal)) ;

      "Should use bedwyr style search on meta-level predicates" >::
        (fun () ->
           let meta_clauses =
             parse_clauses "foo P :- pi c\\ P = conc c => false."
           in
           let goal1 = freshen "foo (hyp A)" in
           let goal2 = freshen "foo (conc A)" in
             assert_search_success (search ~meta_clauses goal1) ;
             assert_search_failure (search ~meta_clauses goal2)) ;

      "Should raise meta clauses over support" >::
        (fun () ->
           let meta_clauses = parse_clauses "foo X." in
           let goal = make_nominals ["x"] (freshen "foo (A x)") in
             assert_search_success (search ~meta_clauses goal)) ;

      "Should raise object clauses over support" >::
        (fun () ->
           let clauses = parse_clauses "foo X." in
           let goal = make_nominals ["x"] (freshen "{foo (A x)}") in
             assert_search_success (search ~clauses goal)) ;

    ]
    
let tests =
  "Tactics" >:::
    [
      object_cut_tests ;
      object_instantiation_tests ;
      apply_tests ;
      case_tests ;
      induction_tests ;
      search_tests ;
    ]
    
