open OUnit
open Test_helper
open Term
open Metaterm
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
             assert_pprint_equal "{L2, L1 |- B}" t) ;

      "Context should be normalized" >::
        (fun () ->
           let h0 = parse_obj "L, A |- B" in
           let h1 = parse_obj "L |- A" in
           let t = object_cut h0 h1 in
             assert_pprint_equal "{L |- B}" t) ;
    ]

let object_instantiation_tests =
  "Object Instantiation" >:::
    [
      "Simple" >::
        (fun () ->
           let t = make_nominals ["n"] (freshen "{eval n B}") in
           let a = var Eigen "A" 0 in
           let result = object_inst t "n" a in
             assert_pprint_equal "{eval A B}" result) ;
      
      "Should only work on nominals" >::
        (fun () ->
           let t = freshen "{prove A}" in
           let b = var Eigen "B" 0 in
           let result = object_inst t "A" b in
             assert_pprint_equal "{prove A}" result) ;
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

      "Properly restricted on predicate" >::
        (fun () ->
           let h0 = freshen "forall A, foo A * -> bar A" in
           let h1 = freshen "foo A *" in
           let t, _ = apply h0 [Some h1] in
             assert_pprint_equal "bar A" t) ;

      "Improperly restricted on predicate" >::
        (fun () ->
           let h0 = freshen "forall A, foo A * -> bar A" in
           let h1 = freshen "foo A @" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply h0 [Some h1])) ;

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

      "On arrow" >::
        (fun () ->
           let h0 = freshen "forall A, (forall B, foo A -> bar B) -> baz A" in
           let h1 = freshen "forall B, foo C -> bar B" in
           let t, _ = apply h0 [Some h1] in
             assert_pprint_equal "baz C" t) ;

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

let case ?used ?(clauses=[]) ?(meta_clauses=[]) term =
  let used =
    match used with
      | None -> metaterm_vars_alist Eigen [term]
      | Some used -> used
  in
    case ~used ~clauses ~meta_clauses term
    
let case_tests =
  "Case" >:::
    [
      "Normal" >::
        (fun () ->
           let term = freshen "{eval A B}" in
             match case ~clauses:eval_clauses term with
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
             match case ~clauses term with
               | [case1] ->
                   set_bind_state case1.bind_state ;
                   begin match case1.new_hyps with
                     | [hyp] ->
                         assert_pprint_equal "{bar A}*" hyp ;
                     | _ -> assert_failure "Expected 1 new hypothesis"
                   end
               | cases -> assert_expected_cases 1 cases) ;

      "Restriction on predicates should become smaller" >::
        (fun () ->
           let term = freshen "foo A @" in
           let meta_clauses = parse_meta_clauses "foo X :- bar X." in
             match case ~meta_clauses term with
               | [case1] ->
                   set_bind_state case1.bind_state ;
                   begin match case1.new_hyps with
                     | [hyp] ->
                         assert_pprint_equal "bar A *" hyp ;
                     | _ -> assert_failure "Expected 1 new hypothesis"
                   end
               | cases -> assert_expected_cases 1 cases) ;

      "Restriction should descend under binders" >::
        (fun () ->
           let term = freshen "foo A @" in
           let meta_clauses = parse_meta_clauses "foo X :- forall Y, bar X." in
             match case ~meta_clauses term with
               | [case1] ->
                   set_bind_state case1.bind_state ;
                   begin match case1.new_hyps with
                     | [hyp] ->
                         assert_pprint_equal "forall Y, bar A *" hyp ;
                     | _ -> assert_failure "Expected 1 new hypothesis"
                   end
               | cases -> assert_expected_cases 1 cases) ;

      "Restriction should descend only under the right of arrows" >::
        (fun () ->
           let term = freshen "foo A @" in
           let meta_clauses = parse_meta_clauses "foo X :- bar X -> baz X." in
             match case ~meta_clauses term with
               | [case1] ->
                   set_bind_state case1.bind_state ;
                   begin match case1.new_hyps with
                     | [hyp] ->
                         assert_pprint_equal "bar A -> baz A *" hyp ;
                     | _ -> assert_failure "Expected 1 new hypothesis"
                   end
               | cases -> assert_expected_cases 1 cases) ;

      "On OR" >::
        (fun () ->
           let term = freshen "{A} \\/ {B}" in
             match case term with
               | [{new_hyps=[hyp1]} ; {new_hyps=[hyp2]}] ->
                   assert_pprint_equal "{A}" hyp1 ;
                   assert_pprint_equal "{B}" hyp2 ;
               | _ -> assert_failure "Pattern mismatch") ;

      "On AND" >::
        (fun () ->
           let term = freshen "{A} /\\ {B}" in
             match case term with
               | [{new_hyps=[hyp1;hyp2]}] ->
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

      "On nabla" >::
        (fun () ->
           let term = freshen "nabla x, foo x" in
           let used = [] in
             match case ~used term with
               | [{new_vars=[] ; new_hyps=[hyp]}] ->
                   assert_pprint_equal "foo n1" hyp ;
               | _ -> assert_failure "Pattern mismatch") ;

      "On nabla with n1 used" >::
        (fun () ->
           let term = make_nominals ["n1"] (freshen "nabla x, foo n1 x") in
           let used = [] in
             match case ~used term with
               | [{new_vars=[] ; new_hyps=[hyp]}] ->
                   assert_pprint_equal "foo n1 n2" hyp ;
               | _ -> assert_failure "Pattern mismatch") ;

      "Should look in context for member" >::
        (fun () ->
           let term = freshen "{L, hyp A |- hyp B}" in
             match case term with
               | [{new_vars=[] ; new_hyps=[hyp]}] ->
                   assert_pprint_equal "member (hyp B) (hyp A :: L)" hyp
               | _ -> assert_failure "Pattern mismatch") ;

      "Should pass along context" >::
        (fun () ->
           let term = freshen "{L |- foo A}" in
           let clauses = parse_clauses "foo X :- bar X." in
             match case ~clauses term with
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
           let meta_clauses =
             parse_meta_clauses ("member A (A :: L)." ^
                                   "member A (B :: L) :- member A L.")
           in
             match case ~meta_clauses term with
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
           let meta_clauses = parse_meta_clauses "pred M N." in
           let term = make_nominals ["n"] (freshen "pred (A n) B") in
             match case ~meta_clauses term with
               | [case1] -> ()
               | cases -> assert_expected_cases 1 cases) ;
             
      "Should raise over nominal variables in clauses" >::
        (fun () ->
           let clauses = parse_clauses "pred M N." in
           let term = make_nominals ["n"] (freshen "{pred (A n) B}") in
             match case ~clauses term with
               | [case1] -> ()
               | cases -> assert_expected_cases 1 cases) ;

      "Should raise when nabla in predicate head" >::
        (fun () ->
           let meta_clauses =
             parse_meta_clauses "nabla x, ctx (var x :: L) :- ctx L." in
           let term = freshen "ctx K" in
             match case ~meta_clauses term with
               | [case1] ->
                   set_bind_state case1.bind_state ;
                   assert_pprint_equal "ctx (var n1 :: L)" term
               | cases -> assert_expected_cases 1 cases) ;
             
    ]

let induction_tests =
  "Induction" >:::
    [
      "Single" >::
        (fun () ->
           let stmt = freshen
               "forall A, {first A} -> {second A} -> {third A}" in
           let (ih, goal) = induction 1 1 stmt in
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
           let (ih, goal) = induction 1 1 stmt in
             assert_pprint_equal
               "forall A, {first A}* -> {second A} -> {third A}" ih ;
             assert_pprint_equal
               "forall A, {first A}@ -> {second A} -> {third A}" goal ;
             let (ih, goal) = induction 2 2 goal in
               assert_pprint_equal
                 "forall A, {first A}@ -> {second A}** -> {third A}" ih ;
               assert_pprint_equal
                 "forall A, {first A}@ -> {second A}@@ -> {third A}" goal) ;
      
      "With OR on left of arrow" >::
        (fun () ->
           let stmt = freshen "forall X, {A} \\/ {B} -> {C} -> {D}" in
           let (ih, goal) = induction 2 1 stmt in
             assert_pprint_equal
               "forall X, {A} \\/ {B} -> {C}* -> {D}"
               ih ;
             assert_pprint_equal
               "forall X, {A} \\/ {B} -> {C}@ -> {D}"
               goal) ;
      
      "On predicate" >::
        (fun () ->
           let stmt = freshen
             "forall A, first A -> second A -> third A" in
           let (ih, goal) = induction 1 1 stmt in
             assert_pprint_equal
               "forall A, first A * -> second A -> third A"
               ih ;
             assert_pprint_equal
               "forall A, first A @ -> second A -> third A"
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

      "On AND" >::
        (fun () ->
           let hyp1 = freshen "{A}" in
           let hyp2 = freshen "{B}" in
           let goal = freshen "{A} /\\ {B}" in
             assert_search_success (search ~hyps:[hyp1; hyp2] goal)) ;

      "On AND (failure)" >::
        (fun () ->
           let hyp = freshen "{A}" in
           let goal = freshen "{A} /\\ {B}" in
             assert_search_failure (search ~hyps:[hyp] goal)) ;

      "On exists" >::
        (fun () ->
           let goal = freshen "exists R, {eq (app M N) R}" in
           let clauses = parse_clauses "eq X X." in
             assert_search_success (search ~clauses goal)) ;

      "Should use meta unification" >::
        (fun () ->
           let hyp1 = freshen "{A} /\\ {B}" in
           let goal = freshen "{A} /\\ {B}" in
             assert_search_success (search ~hyps:[hyp1] goal)) ;
      
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
             parse_meta_clauses
               ("member A (A :: L)." ^
                  "member A (B :: L) :- member A L.")
           in
           let hyp = freshen "member E K" in
           let goal = freshen "member E (F :: K)" in
             assert_search_success (search ~hyps:[hyp] ~meta_clauses goal)) ;

      "Should use bedwyr style search on meta-level predicates" >::
        (fun () ->
           let meta_clauses =
             parse_meta_clauses ("foo P :- forall C, P = conc C -> false." ^
                                   "X = X.")
           in
           let goal1 = freshen "foo (hyp A)" in
           let goal2 = freshen "foo (conc A)" in
             assert_search_success (search ~meta_clauses goal1) ;
             assert_search_failure (search ~meta_clauses goal2)) ;

      "Should find and fail on loops on the left" >::
        (fun () ->
           let meta_clauses = parse_meta_clauses "foo A :- foo A." in
           let goal = freshen "forall X, foo X -> false" in
             assert_search_success (search ~meta_clauses goal)) ;

      "Should raise meta clauses over support" >::
        (fun () ->
           let meta_clauses = parse_meta_clauses "foo X." in
           let goal = make_nominals ["x"] (freshen "foo (A x)") in
             assert_search_success (search ~meta_clauses goal)) ;

      "Should raise object clauses over support" >::
        (fun () ->
           let clauses = parse_clauses "foo X." in
           let goal = make_nominals ["x"] (freshen "{foo (A x)}") in
             assert_search_success (search ~clauses goal)) ;

      "Should work with nabla in the head" >::
        (fun () ->
           let meta_clauses =
             parse_meta_clauses "nabla x, ctx (var x :: L) :- ctx L."
           in
           let hyp = freshen "ctx L" in
           let goal = make_nominals ["n1"] (freshen "ctx (var n1 :: L)") in
             assert_search_success (search ~hyps:[hyp] ~meta_clauses goal)) ;

    ]

let assert_expected_goals n goals =
  assert_failure (Printf.sprintf "Expected %d goal(s) but found %d goal(s)"
                    n (List.length goals))
    
let unfold ?used ~meta_clauses goal =
  let used =
    match used with
      | None -> metaterm_vars_alist Eigen [goal]
      | Some used -> used
  in
    unfold ~used ~meta_clauses goal
    
let unfold_tests =
  "Unfold" >:::
    [
      "Should pick matching clause" >::
        (fun () ->
           let meta_clauses =
             parse_meta_clauses "pred (f X) :- foo X. pred (g X) :- bar X."
           in
           let goal = freshen "pred (g a)" in
             match unfold ~meta_clauses goal with
               | [goal1] -> assert_pprint_equal "bar a" goal1
               | goals -> assert_expected_goals 1 goals) ;

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
      unfold_tests ;
    ]
    
