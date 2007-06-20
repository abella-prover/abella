open OUnit
open Test_helper
open Term
open Lppterm
open Tactics
  
let parse = parse_lppterm

let prog = eval_clauses

let assert_search_success b = assert_bool "Search should succeed" b
let assert_search_failure b = assert_bool "Search should fail" (not b)

let tests =
  "Tactics" >:::
    [
      "Simple object cut" >::
        (fun () ->
           let t = object_cut (parse_obj "A => B") (parse_obj "A") in
             assert_pprint_equal "{B}" t) ;
      
      "Failed object cut" >::
        (fun () ->
           assert_raises_any
             (fun () -> object_cut (parse_obj "A => B") (parse_obj "C"))) ;
      
      "Compound object cut" >::
        (fun () ->
           let h0 = parse_obj "eval A B => typeof B C" in
           let h1 = parse_obj "eval A B" in
           let t = object_cut h0 h1 in
             assert_pprint_equal "{typeof B C}" t) ;

      "Simple object instantiation" >::
        (fun () ->
           let h0 = parse_obj "pi x\\ eval x B" in
           let a = var ~tag:Eigen "A" 0 in
           let t = object_inst h0 a in
             assert_pprint_equal "{eval A B}" t) ;
      
      "Failed object instantiation - missing pi" >::
        (fun () ->
           let h0 = parse_obj "sigma x\\ eval x B" in
           let a = var ~tag:Eigen "A" 0 in
             assert_raises_any
               (fun () -> object_inst h0 a)) ;

      "Failed object instantiation - missing lambda" >::
        (fun () ->
           let h0 = parse_obj "pi eval x B" in
           let a = var ~tag:Eigen "A" 0 in
             assert_raises_any
               (fun () -> object_inst h0 a)) ;

      "Forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B} -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}" in
           let h2 = parse "{typeof (abs R) (arrow S T)}" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Properly restricted forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}* -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}*" in
           let h2 = parse "{typeof (abs R) (arrow S T)}" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;

      "Needlessly restricted forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B} -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}*" in
           let h2 = parse "{typeof (abs R) (arrow S T)}" in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{typeof (abs R) (arrow S T)}" t) ;
      
      "Improperly restricted forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}* -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}" in
           let h2 = parse "{typeof (abs R) (arrow S T)}" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "Improperly inactivated forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B}* -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}@" in
           let h2 = parse "{typeof (abs R) (arrow S T)}" in
             assert_raises (Failure "Restriction violated")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "Unification failure during forall application" >::
        (fun () ->
           let h0 = parse ("forall A B C, " ^
                             "{eval A B} -> {typeof A C} -> {typeof B C}") in
           let h1 = parse "{eval (abs R) (abs R)}" in
           let h2 = parse "{bad (abs R) (arrow S T)}" in
             assert_raises (Failure "Unification failure")
               (fun () -> apply_forall h0 [h1; h2])) ;

      "Forall application with contexts" >::
        (fun () ->
           let h0 = parse
               ("forall E A C," ^
                  "{E, hyp A |- conc C} -> {E |- conc A} -> {E |- conc C}") in
           let h1 = parse "{L, hyp A, hyp B1, hyp B2 |- conc C}" in
           let h2 = parse "{L |- conc A}" in
           let l = var ~tag:Eigen "L" 0 in
           let h1 = replace_lppterm_vars [("L", l)] h1 in
           let h2 = replace_lppterm_vars [("L", l)] h2 in
           let t = apply_forall h0 [h1; h2] in
             assert_pprint_equal "{L, hyp B1, hyp B2 |- conc C}" t) ;

      "Case application" >::
        (fun () ->
           (* eval (abs R) (abs R).
              eval (app M N) V :- eval M (abs R), eval (R N) V.

              case {eval A B} *)
           let a = var ~tag:Eigen "A" 0 in
           let b = var ~tag:Eigen "B" 0 in
           let term = termobj (app (const "eval") [a; b]) in
             match case term prog ["A"; "B"] with
               | [case1; case2] ->
                   case1.set_state () ;
                   assert_pprint_equal "{eval (abs R) (abs R)}" term ;
                   assert_bool "R should be flagged as used"
                     (List.mem "R" (List.map fst case1.new_vars)) ;
                   
                   case2.set_state () ;
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
      
      "Restricted case application" >::
        (fun () ->
           (* eval (abs R) (abs R).
              eval (app M N) V :- eval M (abs R), eval (R N) V.

              case {eval A B} which has Smaller restriction *)
           let a = var ~tag:Eigen "A" 0 in
           let b = var ~tag:Eigen "B" 0 in
           let evalAB = termobj (app (const "eval") [a; b]) in
           let term = apply_restriction Equal evalAB in
             match case term prog ["A"; "B"] with
               | [case1; case2] ->
                   case1.set_state () ;
                   assert_pprint_equal "{eval (abs R) (abs R)}@" term ;
                   
                   case2.set_state () ;
                   assert_pprint_equal "{eval (app M N) B}@" term ;
                   begin match case2.new_hyps with
                     | [h1; h2] ->
                         assert_pprint_equal "{eval M (abs R)}*" h1 ;
                         assert_pprint_equal "{eval (R N) B}*" h2
                     | _ -> assert_failure "Expected 2 new hypotheses"
                   end
               | _ -> assert_failure "Expected 2 cases") ;

      "Case on OR" >::
        (fun () ->
           let term = parse "{A} or {B}" in
           let used = ["A"; "B"] in
             match case term prog used with
               | [{new_hyps=[hyp1]} ; {new_hyps=[hyp2]}] ->
                   assert_pprint_equal "{A}" hyp1 ;
                   assert_pprint_equal "{B}" hyp2 ;
               | _ -> assert_failure "Pattern mismatch") ;

      "Case on exists" >::
        (fun () ->
           let term = parse "exists A B, {eval A B}" in
           let used = [] in
             match case term prog used with
               | [{new_vars=new_vars ; new_hyps=[hyp]}] ->
                   let var_names = List.map fst new_vars in
                     assert_string_list_equal ["A"; "B"] var_names ;
                     assert_pprint_equal "{eval A B}" hyp ;
               | _ -> assert_failure "Pattern mismatch") ;

      "Case on implies" >::
        (fun () ->
           let term = parse "{L |- hyp A => conc B}" in
           let used = [] in
             match case term prog used with
               | [{new_vars=[] ; new_hyps=[hyp]}] ->
                   assert_pprint_equal "{L, hyp A |- conc B}" hyp
               | _ -> assert_failure "Pattern mismatch") ;

      "Case should pass along context" >::
        (fun () ->
           let a = var ~tag:Eigen "A" 0 in
           let b = var ~tag:Eigen "B" 0 in
           let l = var ~tag:Eigen "L" 0 in
           let term = app (const "eval") [a; b] in
           let ctx = Context.add l Context.empty in
           let contexted_term = Obj(context_obj ctx term, Irrelevant) in
             match case contexted_term prog ["A"; "B"] with
               | [case1; case2] ->
                   case1.set_state () ;
                   assert_pprint_equal "{L |- eval (abs R) (abs R)}"
                     contexted_term ;
                   
                   case2.set_state () ;
                   assert_pprint_equal "{L |- eval (app M N) B}"
                     contexted_term ;
                   begin match case2.new_hyps with
                     | [h1; h2] ->
                         assert_pprint_equal "{L |- eval M (abs R)}" h1 ;
                         assert_pprint_equal "{L |- eval (R N) B}" h2 ;
                     | _ -> assert_failure "Expected 2 new hypotheses"
                   end ;
               | _ -> assert_failure "Expected 2 cases") ;

      "Single induction creation" >::
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
      
      "Induction with OR on left of arrow" >::
        (fun () ->
           let stmt = parse "forall X, {A} or {B} -> {C} -> {D}" in
           let (ih, goal) = induction 2 stmt in
             assert_pprint_equal
               "forall X, {A} or {B} -> {C}* -> {D}"
               ih ;
             assert_pprint_equal
               "forall X, {A} or {B} -> {C}@ -> {D}"
               goal) ;
      
      "Search should check hypotheses" >::
        (fun () ->
           let goal = parse "{eval A B}" in
             assert_search_success (search 0 goal prog [goal])) ;
      
      "Search should succeed if clause matches" >::
        (fun () ->
           let goal = parse "{eval (abs R) (abs R)}" in
             assert_search_success (search 1 goal prog [])) ;
      
      "Search should backchain on clauses" >::
        (fun () ->
           let hyp1 = parse "{eval M (abs R)}" in
           let hyp2 = parse "{eval (R N) V}" in
           let goal = parse "{eval (app M N) V}" in
             assert_search_success (search 1 goal prog [hyp1; hyp2])) ;

      "OR left search" >::
        (fun () ->
           let hyp = parse "{eval A B}" in
           let goal = parse "{eval A B} or {false}" in
             assert_search_success (search 0 goal prog [hyp])) ;
      
      "OR right search" >::
        (fun () ->
           let hyp = parse "{eval A B}" in
           let goal = parse "{false} or {eval A B}" in
             assert_search_success (search 0 goal prog [hyp])) ;

      "Exists search" >::
        (fun () ->
           let goal = parse "exists R, {eq (app M N) R}" in
             assert_search_success (search 1 goal prog [])) ;

      "Search should fail if there is no proof" >::
        (fun () ->
           let goal = parse "{eval A B}" in
             assert_search_failure (search 5 goal prog [])) ;
      
      "Search should check context" >::
        (fun () ->
           let goal = parse "{eval A B |- eval A B}" in
             assert_search_success (search 0 goal prog [])) ;

      "Search should fail if hypothesis has non-subcontext" >::
        (fun () ->
           let hyp = parse "{eval A B |- eval A B}" in
           let goal = parse "{eval A B}" in
             assert_search_failure (search 5 goal prog [hyp])) ;

      "Search should preserve context while backchaining" >::
        (fun () ->
           let goal = parse
               "{eval M (abs R), eval (R N) V |- eval (app M N) V}"
           in
             assert_search_success (search 1 goal prog [])) ;

      "Search should move implies to the left" >::
        (fun () ->
           let hyp = parse "{A |- B}" in
           let goal = parse "{A => B}" in
             assert_search_success (search 1 goal prog [hyp])) ;
    ]
