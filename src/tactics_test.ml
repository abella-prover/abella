open OUnit
open Test_helper
open Term
open Lppterm
open Tactics
  
let parse = parse_lppterm

let prog = eval_clauses

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
           let h0 = parse_obj "pi x\\ eval x B" in
           let a = var ~tag:Eigen "A" 0 in
           let t = object_inst h0 a in
             assert_pprint_equal "{eval A B}" t) ;
      
      "Failed - missing pi" >::
        (fun () ->
           let h0 = parse_obj "sigma x\\ eval x B" in
           let a = var ~tag:Eigen "A" 0 in
             assert_raises_any
               (fun () -> object_inst h0 a)) ;

      "Failed - missing lambda" >::
        (fun () ->
           let h0 = parse_obj "pi eval x B" in
           let a = var ~tag:Eigen "A" 0 in
             assert_raises_any
               (fun () -> object_inst h0 a)) ;
    ]

let forall_application_tests =
  "Forall Application" >:::
    [
      "Normal" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B} -> {typeof A C} -> {typeof B C}") in
           let h1 = freshen "{eval (abs R) (abs R)}" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Properly restricted" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}* -> {typeof A C} -> {typeof B C}") in
           let h1 = freshen "{eval (abs R) (abs R)}*" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Needlessly restricted" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B} -> {typeof A C} -> {typeof B C}") in
           let h1 = freshen "{eval (abs R) (abs R)}*" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;
      
      "Improperly restricted" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}* -> {typeof A C} -> {typeof B C}") in
           let h1 = freshen "{eval (abs R) (abs R)}" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "Improperly restricted (2)" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}* -> {typeof A C} -> {typeof B C}") in
           let h1 = freshen "{eval (abs R) (abs R)}@" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "Properly double restricted" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}@ -> {typeof A C}** -> {typeof B C}") in
           let h1 = freshen "{eval (abs R) (abs R)}@" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}**" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Improperly double restricted" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}@ -> {typeof A C}** -> {typeof B C}") in
           let h1 = freshen "{eval (abs R) (abs R)}@" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}@@" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "Improperly double restricted (2)" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}@ -> {typeof A C}** -> {typeof B C}") in
           let h1 = freshen "{eval (abs R) (abs R)}" in
           let h2 = freshen "{typeof (abs R) (arrow S T)}**" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "Unification failure" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B} -> {typeof A C} -> {typeof B C}") in
           let h1 = freshen "{eval (abs R) (abs R)}" in
           let h2 = freshen "{bad (abs R) (arrow S T)}" in
             assert_raises (Failure "Unification failure")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "With contexts" >::
        (fun () ->
           let h0 = parse
               ("forall E A C," ^
                  "{E, hyp A |- conc C} -> {E |- conc A} -> {E |- conc C}") in
           let h1 = freshen "{L, hyp A, hyp B1, hyp B2 |- conc C}" in
           let h2 = freshen "{L |- conc A}" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{L, hyp B1, hyp B2 |- conc C}" t) ;

      "On non-object" >::
        (fun () ->
           let h0 = parse "forall A, pred A -> result A" in
           let h1 = freshen "pred B" in
           let t = apply_forall h0 [h1] in
             assert_pprint_equal "result B" t) ;
    ]

let case_application_tests =
  "Case Application" >:::
    [
      "Normal" >::
        (fun () ->
           let term = freshen "{eval A B}" in
             match case term prog [] ["A"; "B"] with
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
               | _ -> assert_failure "Expected 2 cases") ;
      
      "Restriction should become smaller" >::
        (fun () ->
           let term = freshen "{eval A B}@" in
             match case term prog [] ["A"; "B"] with
               | [case1; case2] ->
                   set_bind_state case1.bind_state ;
                   assert_pprint_equal "{eval (abs R) (abs R)}@" term ;
                   
                   set_bind_state case2.bind_state ;
                   assert_pprint_equal "{eval (app M N) B}@" term ;
                   begin match case2.new_hyps with
                     | [h1; h2] ->
                         assert_pprint_equal "{eval M (abs R)}*" h1 ;
                         assert_pprint_equal "{eval (R N) B}*" h2
                     | _ -> assert_failure "Expected 2 new hypotheses"
                   end
               | _ -> assert_failure "Expected 2 cases") ;

      "On OR" >::
        (fun () ->
           let term = freshen "{A} or {B}" in
           let used = ["A"; "B"] in
             match case term prog [] used with
               | [{new_hyps=[hyp1]} ; {new_hyps=[hyp2]}] ->
                   assert_pprint_equal "{A}" hyp1 ;
                   assert_pprint_equal "{B}" hyp2 ;
               | _ -> assert_failure "Pattern mismatch") ;

      "On exists" >::
        (fun () ->
           let term = parse "exists A B, {eval A B}" in
           let used = [] in
             match case term prog [] used with
               | [{new_vars=new_vars ; new_hyps=[hyp]}] ->
                   let var_names = List.map fst new_vars in
                     assert_string_list_equal ["A"; "B"] var_names ;
                     assert_pprint_equal "{eval A B}" hyp ;
               | _ -> assert_failure "Pattern mismatch") ;

      "On implies" >::
        (fun () ->
           let term = freshen "{L |- hyp A => conc B}" in
           let used = [] in
             match case term prog [] used with
               | [{new_vars=[] ; new_hyps=[hyp]}] ->
                   assert_pprint_equal "{L, hyp A |- conc B}" hyp
               | _ -> assert_failure "Pattern mismatch") ;

      "Should pass along context" >::
        (fun () ->
           let term = freshen "{L |- eval A B}" in
             match case term prog [] ["A"; "B"] with
               | [case1; case2; case3] ->
                   (* case1 is the member case *)
                   
                   set_bind_state case2.bind_state ;
                   assert_pprint_equal "{L |- eval (abs R) (abs R)}" term ;
                   
                   set_bind_state case3.bind_state ;
                   assert_pprint_equal "{L |- eval (app M N) B}" term ;
                   begin match case3.new_hyps with
                     | [h1; h2] ->
                         assert_pprint_equal "{L |- eval M (abs R)}" h1 ;
                         assert_pprint_equal "{L |- eval (R N) B}" h2 ;
                     | _ -> assert_failure "Expected 2 new hypotheses"
                   end ;
               | _ -> assert_failure "Expected 3 cases") ;

      "Should look in context for member" >::
        (fun () ->
           let term = freshen "{L, hyp A |- hyp B}" in
           let used = ["L"; "A"; "B"] in
             match case term prog [] used with
               | [{new_vars=[] ; new_hyps=[hyp]}] ->
                   assert_pprint_equal "member (hyp B) (hyp A :: L)" hyp
               | _ -> assert_failure "Pattern mismatch") ;

      "On member" >::
        (fun () ->
           let term = freshen "member (hyp A) (hyp C :: L)" in
           let used = ["A"; "C"; "L"] in
           let member_clauses =
               parse_clauses ("member A (A :: L)." ^
                                "member A (B :: L) :- member A L.")
           in
             match case term prog member_clauses used with
               | [case1; case2] ->
                   set_bind_state case1.bind_state ;
                   assert_pprint_equal "member (hyp C) (hyp C :: L)" term ;

                   set_bind_state case2.bind_state ;
                   begin match case2.new_hyps with
                     | [hyp] ->
                         assert_pprint_equal "member (hyp A) L" hyp ;
                     | _ -> assert_failure "Expected 1 new hypothesis"
                   end
               | _ -> assert_failure "Expected two cases") ;
    ]

let induction_tests =
  "Induction" >:::
    [
      "Single" >::
        (fun () ->
           let stmt = parse
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
           let stmt = parse
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
           let stmt = parse "forall X, {A} or {B} -> {C} -> {D}" in
           let (ih, goal) = induction 2 stmt in
             assert_pprint_equal
               "forall X, {A} or {B} -> {C}* -> {D}"
               ih ;
             assert_pprint_equal
               "forall X, {A} or {B} -> {C}@ -> {D}"
               goal) ;
    ]

let assert_search_success b = assert_bool "Search should succeed" b
let assert_search_failure b = assert_bool "Search should fail" (not b)
let basic_search n hyps goal =
  search ~depth:n ~hyps:hyps ~clauses:prog ~meta_clauses:[] ~goal:goal
  
let search_tests =
  "Search" >:::
    [
      "Should check hypotheses" >::
        (fun () ->
           let goal = freshen "{eval A B}" in
             assert_search_success (basic_search 0 [goal] goal)) ;
      
      "Should should succeed if clause matches" >::
        (fun () ->
           let goal = freshen "{eval (abs R) (abs R)}" in
             assert_search_success (basic_search 1 [] goal)) ;
      
      "Should backchain on clauses" >::
        (fun () ->
           let hyp1 = freshen "{eval M (abs R)}" in
           let hyp2 = freshen "{eval (R N) V}" in
           let goal = freshen "{eval (app M N) V}" in
             assert_search_success (basic_search 1 [hyp1; hyp2] goal)) ;

      "On left of OR" >::
        (fun () ->
           let hyp = freshen "{eval A B}" in
           let goal = freshen "{eval A B} or {false}" in
             assert_search_success (basic_search 0 [hyp] goal)) ;
      
      "On right of OR" >::
        (fun () ->
           let hyp = freshen "{eval A B}" in
           let goal = freshen "{false} or {eval A B}" in
             assert_search_success (basic_search 0 [hyp] goal)) ;

      "On exists" >::
        (fun () ->
           let goal = freshen "exists R, {eq (app M N) R}" in
             assert_search_success (basic_search 1 [] goal)) ;

      "Should fail if there is no proof" >::
        (fun () ->
           let goal = freshen "{eval A B}" in
             assert_search_failure (basic_search 5 [] goal)) ;
      
      "Should check context" >::
        (fun () ->
           let goal = freshen "{eval A B |- eval A B}" in
             assert_search_success (basic_search 0 [] goal)) ;

      "Should fail if hypothesis has non-subcontext" >::
        (fun () ->
           let hyp = freshen "{eval A B |- eval A B}" in
           let goal = freshen "{eval A B}" in
             assert_search_failure (basic_search 5 [hyp] goal)) ;

      "Should preserve context while backchaining" >::
        (fun () ->
           let goal = freshen
               "{eval M (abs R), eval (R N) V |- eval (app M N) V}"
           in
             assert_search_success (basic_search 1 [] goal)) ;

      "Should move implies to the left" >::
        (fun () ->
           let hyp = freshen "{A |- B}" in
           let goal = freshen "{A => B}" in
             assert_search_success (basic_search 1 [hyp] goal)) ;

      "Should look for member" >::
        (fun () ->
           let hyp = freshen "member (hyp A) L" in
           let goal = freshen "{L |- hyp A}" in
             assert_search_success (basic_search 1 [hyp] goal)) ;

      "Should backchain on meta-clauses" >::
        (fun () ->
           let meta_clauses =
             parse_clauses
               ("member A (A :: L)." ^
                  "member A (B :: L) :- member A L.")
           in
           let hyp = freshen "member E K" in
           let goal = freshen "member E (F :: K)" in
             assert_search_success
               (search ~depth:5 ~hyps:[hyp]
                  ~clauses:[] ~meta_clauses:meta_clauses
                  ~goal:goal)) ;

      "Should use bedwyr style search on meta-level predicates" >::
        (fun () ->
           let meta_clauses =
             parse_clauses "pred P :- pi c\\ P = conc c => false."
           in
           let meta_search goal =
             search ~depth:10 ~hyps:[] ~clauses:[]
               ~meta_clauses:meta_clauses ~goal:goal
           in
           let goal1 = freshen "pred (hyp A)" in
           let goal2 = freshen "pred (conc A)" in
             assert_search_success (meta_search goal1) ;
             assert_search_failure (meta_search goal2)) ;
    ]
    
let tests =
  "Tactics" >:::
    [
      object_cut_tests ;
      object_instantiation_tests ;
      forall_application_tests ;
      case_application_tests ;
      induction_tests ;
      search_tests ;
    ]
      
