open OUnit
open Test_helper
open Metaterm
open Prover
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

let assert_goal goal =
  assert_string_equal goal (metaterm_to_string sequent.goal)

let setup_prover ?clauses:(clauses=[]) ?goal:(goal="") ?lemmas:(lemmas=[]) () =
  full_reset_prover () ;
  add_clauses clauses ;
  if goal <> "" then Prover.sequent.goal <- parse_metaterm goal ;
  Prover.lemmas :=
    List.map (fun (name,body) -> (name, parse_metaterm body)) lemmas

let tests =
  "Prover" >:::
    [
      "New variables added to context" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses ;

           sequent.hyps <- [("H1", freshen "{eval A B}")] ;
           case "H1" ;
           assert_bool "R should be added to variable list"
             (List.mem_assoc "R" sequent.vars)
        ) ;

      "Intros should raise over support" >::
        (fun () ->
           setup_prover ()
             ~goal:"forall L, foo n1 L" ;
           sequent.goal <- make_nominals ["n1"] sequent.goal ;

           intros () ;
           assert_goal "foo n1 (L n1)"
        ) ;
           
      "Assert test" >::
        (fun () ->
           setup_prover ()
             ~goal:"{pred A}" ;
           
           assert_hyp (freshen "{pred B}") ;
           assert_n_subgoals 2 ;

           assert_pprint_equal "{pred B}" sequent.goal ;
           skip () ;
           assert_n_subgoals 1 ;

           assert_pprint_equal "{pred A}" sequent.goal ;
           match sequent.hyps with
             | [(_, hyp)] -> assert_pprint_equal "{pred B}" hyp
             | _ -> assert_failure "Expected one hypothesis"
        ) ;

      "Split test" >::
        (fun () ->
           setup_prover ()
             ~goal:"{A} /\\ {B}" ;

           split () ;
           assert_n_subgoals 2 ;

           assert_pprint_equal "{A}" sequent.goal ;

           skip () ;
           match sequent.hyps with
             | [(_, t)] ->
                 assert_pprint_equal "{A}" t ;
                 assert_pprint_equal "{B}" sequent.goal
             | _ -> assert_failure "Expected one hypothesis" ) ;

      "Exists test" >::
        (fun () ->
           setup_prover ()
             ~goal:"exists A, {foo A}" ;

           exists (parse_term "X") ;

           assert_pprint_equal "{foo X}" sequent.goal) ;

      "System should know about term equality" >::
        (fun () ->
           setup_prover ()
             ~goal:"{A = A}" ;

           assert_proof search) ;

      "Obligations from apply should be added as subgoals" >::
        (fun () ->
           setup_prover ()
             ~goal:"{third B}" ;

           sequent.hyps <-
             [("H1", freshen ("forall A," ^
                                "{first A} -> {second A} -> {third A}")) ;
              ("H2", freshen "{first B}")] ;

           assert_n_subgoals 1 ;
           
           apply "H1" ["H2"; "_"] ;
           assert_n_subgoals 2 ;
           assert_pprint_equal "{second B}" sequent.goal ;
           
           skip () ;
           assert_n_subgoals 1 ;
           assert_pprint_equal "{third B}" sequent.goal ;
        );
      
      "Cases should not consume fresh hyp names" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V, {typeof P V} -> {typeof P V}" ;

           intros () ;
           case ~keep:true "H1" ;
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

      "Add example (lemmas)" >::
        (fun () ->
           let addition_clauses = parse_clauses "
             add z N N.
             add (s A) B (s C) :- add A B C.
             nat z.
             nat (s N) :- nat N."
           in
             setup_prover ()
               ~clauses:addition_clauses
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
               ~goal:"forall X, {foo X} -> {eq X a} \\/ {eq X b}" ;
             
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
               ~goal:"forall X, {eq X a} \\/ {eq X b} -> {foo X}" ;
             
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
               ~goal:"forall X, {nat X} -> {even X} \\/ {odd X}" ;
             
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
