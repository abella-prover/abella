open OUnit
open Test_helper
open Term
open Lppterm
open Tactics
  
let parse = parse_lppterm

let prog = eval_clauses

let assert_search_success f = assert_bool "Search should succeed" f
    
let tests =
  "Tactics" >:::
    [
      "Simple object cut" >::
        (fun () ->
           let t = object_cut (parse "{A => B}") (parse "{A}") in
             assert_pprint_equal "{B}" t) ;
      
      "Failed object cut" >::
        (fun () ->
           assert_raises_any
             (fun () -> object_cut (parse "{A => B}") (parse "{C}"))) ;
      
      "Compound object cut" >::
        (fun () ->
           let h0 = parse "{eval A B => typeof B C}" in
           let h1 = parse "{eval A B}" in
           let t = object_cut h0 h1 in
             assert_pprint_equal "{typeof B C}" t) ;

      "Simple object instantiation" >::
        (fun () ->
           let h0 = parse "{pi x\\ eval x B}" in
           let a = var ~tag:Eigen "A" 0 in
           let t = object_inst h0 a in
             assert_pprint_equal "{eval A B}" t) ;
      
      "Failed object instantiation - missing pi" >::
        (fun () ->
           let h0 = parse "{sigma x\\ eval x B}" in
           let a = var ~tag:Eigen "A" 0 in
             assert_raises_any
               (fun () -> object_inst h0 a)) ;

      "Failed object instantiation - missing lambda" >::
        (fun () ->
           let h0 = parse "{pi eval x B}" in
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

      "Case application" >::
        (fun () ->
           (* eval (abs R) (abs R).
              eval (app M N) V :- eval M (abs R), eval (R N) V.

              case {eval A B} *)
           let a = var ~tag:Eigen "A" 0 in
           let b = var ~tag:Eigen "B" 0 in
           let term = obj (app (const "eval") [a; b]) in
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
           let evalAB = obj (app (const "eval") [a; b]) in
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
      
      "0-step search" >::
        (fun () ->
           let term = parse "{eval A B}" in
           let vars = ["A"; "B"] in
             assert_search_success (search 0 term prog vars [term])) ;
      
      "1-step search with no body" >::
        (fun () ->
           let goal = parse "{eval (abs R) (abs R)}" in
           let vars = ["R"] in
             assert_search_success (search 1 goal prog vars [])) ;
      
      "1-step search with body" >::
        (fun () ->
           let hyp1 = parse "{eval M (abs R)}" in
           let hyp2 = parse "{eval (R N) V}" in
           let goal = parse "{eval (app M N) V}" in
           let vars = ["M"; "N"; "V"; "R"] in
             assert_search_success (search 1 goal prog vars [hyp1; hyp2])) ;

      "OR left search" >::
        (fun () ->
           let hyp = parse "{eval A B}" in
           let term = parse "{eval A B} or {false}" in
           let vars = ["A"; "B"] in
             assert_search_success (search 0 term prog vars [hyp])) ;
      
      "OR right search" >::
        (fun () ->
           let hyp = parse "{eval A B}" in
           let term = parse "{false} or {eval A B}" in
           let vars = ["A"; "B"] in
             assert_search_success (search 0 term prog vars [hyp])) ;

      "Exists search" >::
        (fun () ->
           let term = parse "exists R, {eq (app M N) R}" in
           let vars = ["M"; "N"] in
             assert_search_success (search 1 term prog vars [])) ;
      
    ]
