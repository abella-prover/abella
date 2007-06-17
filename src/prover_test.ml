open OUnit
open Test_helper
open Prover
open Lppterm
open Term

let assert_n_subgoals n =
  if n <> 1 + List.length !subgoals then
    assert_failure ("Expected " ^ (string_of_int n) ^ " subgoal(s), " ^
                      "but current proof state is,\n\n" ^ get_display ())

let assert_proof proof_function =
  try
    proof_function () ;
    assert_failure ("Proof not completed,\n\n" ^ get_display ())
  with Failure("Proof completed.") -> ()

let setup_prover ?clauses:(clauses=[]) ?goal:(goal="") ?lemmas:(lemmas=[]) () =
  reset_prover () ;
  Prover.clauses := clauses ;
  if goal <> "" then Prover.sequent.goal <- parse_lppterm goal ;
  Prover.lemmas :=
    List.map (fun (name,body) -> (name, parse_lppterm body)) lemmas

let freshen str =
  match Tactics.freshen_capital_vars Eigen [parse_term str] [] with
    | [fresh] -> termobj fresh
    | _ -> assert false
  
let tests =
  "Prover" >:::
    [
      "New variables added to context" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses ;

           sequent.hyps <- [("H1", freshen "eval A B")] ;
           case "H1" ;
           assert_bool "R should be added to variable list"
             (List.mem "R" (var_names ())) ;
        ) ;
      
      "Subject reduction for eval example" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V T, {eval P V} -> {typeof P T} -> {typeof V T}" ;

           assert_proof
             (fun () ->
                induction 1 ;
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
                search () ;
             )
        ) ;

      "Progress for eval example" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P T, {typeof P T} -> {progress P}" ;

           assert_proof
             (fun () ->
                induction 1 ;
                intros () ;
                case "H1" ;
                assert_n_subgoals 2 ;
                
                search () ;
                assert_n_subgoals 1 ;
                
                apply "IH" ["H2"] ;
                case "H4" ;
                assert_n_subgoals 2 ;
                
                case "H5" ;
                search () ;
                assert_n_subgoals 1 ;
                
                search () ;
             )
        ) ;

      "Progress for eval example (without explicit progress predicate)" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:("forall P T, {typeof P T} -> " ^
                      "{value P} or exists P', {step P P'}") ;

           assert_proof
             (fun () ->
                induction 1 ;
                intros () ;
                case "H1" ;
                assert_n_subgoals 2 ;
                
                search () ;
                assert_n_subgoals 1 ;

                apply "IH" ["H2"] ;
                case "H4" ;
                assert_n_subgoals 2 ;

                case "H5" ;
                search () ;
                assert_n_subgoals 1 ;

                case "H5" ;
                search () ;
             )
        ) ;

      "Cases should not consume fresh hyp names" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V, {typeof P V} -> {typeof P V}" ;

           intros () ;
           case "H1" ;
           assert_n_subgoals 2 ;
           assert_string_list_equal ["H1"; "H2"] (List.map fst sequent.hyps) ;
           
           search () ;
           assert_n_subgoals 1 ;

           assert_string_list_equal
             ["H1"; "H2"; "H3"] (List.map fst sequent.hyps)           
        ) ;

      "Skip should remove current subcase" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V, {typeof P V} -> {typeof P V}" ;

           intros () ;
           case "H1" ;
           assert_n_subgoals 2 ;
           
           skip () ;
           assert_n_subgoals 1 ;
        ) ;

      "PCF example" >::
        (fun () ->
           setup_prover ()
             ~clauses:pcf_clauses
             ~goal:"forall P V T, {eval P V} -> {typeof P T} -> {typeof V T}" ;

           assert_proof
             (fun () ->
                induction 1 ;
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
                search () ;
             )
        ) ;
      
      "Failed unification during case" >::
        (fun () ->
           setup_prover ()
             ~clauses:fsub_clauses ;

           sequent.hyps <- [("H1", freshen "sub S top")] ;
           case "H1" ;
           assert_n_subgoals 2 ;
        ) ;

      "Add example (lemmas)" >::
        (fun () ->
           setup_prover ()
             ~clauses:add_clauses
             ~goal:"forall A B C, {nat B} -> {add A B C} -> {add B A C}"
             ~lemmas:[
               ("base", "forall N, {nat N} -> {add N z N}") ;
               ("step", "forall A B C, {add A B C} -> {add A (s B) (s C)}")] ;

           assert_proof
             (fun () ->
                induction 2 ;
                intros () ;
                case "H2" ;
                assert_n_subgoals 2 ;
                
                apply "base" ["H1"] ;
                search () ;
                assert_n_subgoals 1 ;
                
                apply "IH" ["H1"; "H3"] ;
                apply "step" ["H4"] ;
                search () ;
             )
        ) ;

      "Undo should restore previous state" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V T, {eval P V} -> {typeof P T} -> {typeof V T}" ;

           induction 1 ;
           intros () ;
           assert_n_subgoals 1 ;
           
           case "H1" ;
           assert_n_subgoals 2 ;
           
           undo () ;
           assert_n_subgoals 1 ;

           case "H1" ;
           assert_n_subgoals 2 ;
        ) ;
             
      "Proving OR" >::
        (fun () ->
           let clauses = parse_clauses "foo a. foo b. eq X X." in
             
             setup_prover ()
               ~clauses:clauses
               ~goal:"forall X, {foo X} -> {eq X a} or {eq X b}" ;
             
             assert_proof
               (fun () ->
                  induction 1 ;
                  intros () ;
                  
                  case "H1" ;
                  assert_n_subgoals 2 ;
                  
                  search () ;
                  assert_n_subgoals 1 ;
                  
                  search () ;
               )
        ) ;

      "OR on left side of arrow" >::
        (fun () ->
           let clauses = parse_clauses "foo a. foo b. eq X X." in
             
             setup_prover ()
               ~clauses:clauses
               ~goal:"forall X, {eq X a} or {eq X b} -> {foo X}" ;
             
             assert_proof
               (fun () ->
                  intros () ;
                  case "H1" ;
                  assert_n_subgoals 2 ;

                  case "H2" ;
                  search () ;

                  case "H2" ;
                  search () ;
               )
        ) ;
      
      "Using IH with OR" >::
        (fun () ->
           let clauses = parse_clauses
             ("nat z. nat (s X) :- nat X." ^
                "even z. even (s X) :- odd X." ^
                "odd (s z). odd (s X) :- even X.") in
             
             setup_prover ()
               ~clauses:clauses
               ~goal:"forall X, {nat X} -> {even X} or {odd X}" ;
             
             assert_proof
               (fun () ->
                  induction 1 ;
                  intros () ;
                  
                  case "H1" ;
                  assert_n_subgoals 2 ;

                  search () ;
                  assert_n_subgoals 1 ;

                  apply "IH" ["H2"] ;
                  case "H3" ;
                  assert_n_subgoals 2 ;

                  search () ;
                  assert_n_subgoals 1 ;

                  search () ;
               )
        ) ;

    ]
