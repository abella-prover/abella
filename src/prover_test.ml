open OUnit
open Test_helper
open Prover
open Lppterm
open Term

let parse = parse_lppterm

let assert_string_list_equal lst1 lst2 =
  assert_int_equal (List.length lst1) (List.length lst2) ;
  ignore (List.map2 (assert_equal ~printer:(fun s -> s)) lst1 lst2)

let assert_n_subgoals n = assert_int_equal n (1 + List.length !subgoals)
    
 let tests =
  "Prover" >:::
    [
      "New variables added to context" >::
        (fun () ->
           reset_prover () ;
           Prover.clauses := eval_clauses ;
           match Tactics.freshen_capital_vars
             Eigen [parse "{eval A B}"] [] with
               | [hyp] ->
                   hyps := [("H1", hyp)] ;
                   case "H1" ;
                   assert_bool "R should be added to variable list"
                     (List.mem "R" (var_names ())) ;
               | _ -> assert false
        ) ;
      
      "Eval example" >::
        (fun () ->
           reset_prover () ;
           Prover.clauses := eval_clauses ;
           goal := parse ("forall P V T, " ^
                            "{eval P V} -> {typeof P T} -> {typeof V T}") ;

           induction [1] ;
           intros () ;
           case "H1" ;
           assert_n_subgoals 2 ;
           
           search () ;
           assert_n_subgoals 1 ;

           case "H2" ;
           apply "IH" ["H3"; "H5"] ;
           case "H7" ;
           inst "H8" (parse_term "N") ;

           apply "H9" ["H6"] ;
           apply "IH" ["H4"; "H10"] ;
           assert_raises (Failure("Proof completed."))
             search ;
        ) ;

      "Cases should not consume fresh hyp names" >::
        (fun () ->
           reset_prover () ;
           Prover.clauses := eval_clauses ;
           goal := parse ("forall P V, {typeof P V} -> {typeof P V}") ;

           intros () ;
           case "H1" ;
           assert_n_subgoals 2 ;
           assert_string_list_equal ["H1"; "H2"] (List.map fst !hyps) ;
           
           search () ;
           assert_n_subgoals 1 ;

           assert_string_list_equal
             ["H1"; "H2"; "H3"] (List.map fst !hyps)           
        ) ;

      "PCF example" >::
        (fun () ->
           reset_prover () ;
           Prover.clauses := pcf_clauses ;
           goal := parse ("forall P V T, " ^
                            "{eval P V} -> {typeof P T} -> {typeof V T}") ;

           induction [1] ;
           intros () ;
           case "H1" ;
           assert_n_subgoals 13 ;
           
           search () ;
           assert_n_subgoals 12 ;

           search () ;
           assert_n_subgoals 11 ;

           search () ;
           assert_n_subgoals 10 ;

           case "H2" ;
           apply "IH" ["H3"; "H4"] ;
           search () ;
           assert_n_subgoals 9 ;

           case "H2" ;
           search () ;
           assert_n_subgoals 8 ;

           case "H2" ;
           apply "IH" ["H3"; "H4"] ;
           case "H5" ;
           search () ;
           assert_n_subgoals 7 ;

           case "H2" ;
           search () ;
           assert_n_subgoals 6 ;

           case "H2" ;
           search () ;
           assert_n_subgoals 5 ;

           case "H2" ;
           apply "IH" ["H4"; "H6"] ;
           search () ;
           assert_n_subgoals 4 ;

           case "H2" ;
           apply "IH" ["H4"; "H7"] ;
           search () ;
           assert_n_subgoals 3 ;

           search () ;
           assert_n_subgoals 2 ;

           case "H2" ;
           apply "IH" ["H3"; "H5"] ;
           case "H7" ;
           inst "H8" (parse_term "N") ;
           apply "H9" ["H6"] ;
           apply "IH" ["H4"; "H10"] ;
           search () ;
           assert_n_subgoals 1 ;

           case "H2" ;
           inst "H4" (parse_term "rec T R") ;
           apply "H5" ["H2"] ;
           apply "IH" ["H3"; "H6"] ;
           assert_raises (Failure("Proof completed."))
             search ;
        ) ;
      
      "Failed unification during case" >::
        (fun () ->
           reset_prover () ;
           Prover.clauses := fsub_clauses ;
           match Tactics.freshen_capital_vars
             Eigen [parse "{sub S top}"] [] with
               | [hyp] ->
                   hyps := [("H1", hyp)] ;
                   case "H1" ;
                   assert_n_subgoals 2 ;
               | _ -> assert false
        ) ;
    ]
