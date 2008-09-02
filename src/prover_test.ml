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

let setup_prover ?clauses:(clauses=[])
    ?goal:(goal="") ?lemmas:(lemmas=[]) () =
  full_reset_prover () ;
  add_clauses clauses ;
  if goal <> "" then Prover.sequent.goal <- freshen goal ;
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

           intros () ;
           assert_goal "foo n1 (L n1)"
        ) ;

      "Intros on multiple nabla variables" >::
        (fun () ->
           setup_prover ()
             ~goal:"nabla x y, x = y" ;

           intros () ;
           assert_goal "n1 = n2"
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

           split false ;
           assert_n_subgoals 2 ;

           assert_pprint_equal "{A}" sequent.goal ;

           skip () ;
           match sequent.hyps with
             | [] -> assert_pprint_equal "{B}" sequent.goal
             | _ -> assert_failure "Expected no hypotheses"
        ) ;

      "SplitStar test" >::
        (fun () ->
           setup_prover ()
             ~goal:"{A} /\\ {B}" ;

           split true ;
           assert_n_subgoals 2 ;

           assert_pprint_equal "{A}" sequent.goal ;

           skip () ;
           match sequent.hyps with
             | [(_, t)] ->
                 assert_pprint_equal "{A}" t ;
                 assert_pprint_equal "{B}" sequent.goal
             | _ -> assert_failure "Expected one hypothesis"
        ) ;

      "Split many test" >::
        (fun () ->
           setup_prover ()
             ~goal:"({A} /\\ {B}) /\\ ({C} /\\ {D})" ;

           split false ;
           assert_n_subgoals 4 ;

           assert_pprint_equal "{A}" sequent.goal ;
           skip () ;
           assert_pprint_equal "{B}" sequent.goal ;
           skip () ;
           assert_pprint_equal "{C}" sequent.goal ;
           skip () ;
           assert_pprint_equal "{D}" sequent.goal
        ) ;

      "SplitStar many test" >::
        (fun () ->
           setup_prover ()
             ~goal:"{A} /\\ {B} /\\ {C}" ;

           split true ;
           assert_n_subgoals 3 ;

           assert_pprint_equal "{A}" sequent.goal ;

           skip () ;
           begin match sequent.hyps with
             | [(_, t)] ->
                 assert_pprint_equal "{A}" t ;
                 assert_pprint_equal "{B}" sequent.goal
             | _ -> assert_failure "Expected one hypothesis"
           end ;

           skip () ;
           begin match sequent.hyps with
             | [(_, t1); (_, t2)] ->
                 assert_pprint_equal "{A}" t1 ;
                 assert_pprint_equal "{B}" t2 ;
                 assert_pprint_equal "{C}" sequent.goal
             | _ -> assert_failure "Expected two hypotheses"
           end
        ) ;

      "Needless split" >::
        (fun () ->
           setup_prover ()
             ~goal:"{A}" ;

           assert_raises (Failure "Needless use of split")
             (fun () -> split false)
        ) ;

      "Exists test" >::
        (fun () ->
           setup_prover ()
             ~goal:"exists A, {foo A}" ;

           exists (parse_term "X") ;

           assert_pprint_equal "{foo X}" sequent.goal) ;

      "Obligations from apply should be added as subgoals" >::
        (fun () ->
           setup_prover ()
             ~goal:"{third B}" ;

           sequent.hyps <-
             [("H1", freshen ("forall A," ^
                                "{first A} -> {second A} -> {third A}")) ;
              ("H2", freshen "{first B}")] ;

           assert_n_subgoals 1 ;

           apply "H1" ["H2"; "_"] [] ;
           assert_n_subgoals 2 ;
           assert_pprint_equal "{second B}" sequent.goal ;

           skip () ;
           assert_n_subgoals 1 ;
           assert_pprint_equal "{third B}" sequent.goal ;
        );

      "Apply should trigger case analysis" >::
        (fun () ->
           setup_prover () ;

           add_hyp (freshen "forall A, foo A -> bar A /\\ baz A") ;
           add_hyp (freshen "foo B") ;

           apply "H1" ["H2"] [] ;
           assert_pprint_equal "bar B" (List.assoc "H3" sequent.hyps) ;
           assert_pprint_equal "baz B" (List.assoc "H4" sequent.hyps)
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
                  induction [2] ;
                  intros () ;
                  case "H2" ;
                  assert_n_subgoals 2 ;

                  apply "base" ["H1"] [] ;
                  search () ;
                  assert_n_subgoals 1 ;

                  apply "IH" ["H1"; "H3"] [] ;
                  apply "step" ["H4"] [] ;
                  search () ;
               )
        ) ;

      "Undo should restore previous save state" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V T, {eval P V} -> {typeof P T} -> {typeof V T}" ;

           induction [1] ;
           intros () ;
           assert_n_subgoals 1 ;

           save_undo_state () ;
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
                  induction [1] ;
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
                  induction [1] ;
                  intros () ;

                  case "H1" ;
                  assert_n_subgoals 2 ;

                  search () ;
                  assert_n_subgoals 1 ;

                  apply "IH" ["H2"] [] ;
                  case "H3" ;
                  assert_n_subgoals 2 ;

                  search () ;
                  assert_n_subgoals 1 ;

                  search () ;
               )
        ) ;

      "Unification error during case analysis should propogate to toplevel" >::
        (fun () ->
           setup_prover ()
             ~clauses:(parse_clauses "pred (X Y).") ;

           sequent.hyps <- [("H1", freshen "{pred (A B)}")] ;
           try
             case "H1" ;
             assert_failure "Case analysis did not fail"
           with
             | Failure("Unification error during case analysis") -> ()
             | _ -> assert_failure "Case analysis did not fail"
        ) ;

      "Toplevel logic variable should produce error in apply" >::
        (fun () ->
           setup_prover () ;

           add_hyp (freshen "forall A, {foo} -> {bar A}") ;
           add_hyp (freshen "{foo}") ;

           try
             apply "H1" ["H2"] [] ;
             assert_failure ("Logic variable did not produce error\n\n" ^
                               get_display ())
           with
             | Failure("Found logic variable at toplevel") -> ()
        ) ;

      "Search should not find the inductive hypothesis" >::
        (fun () ->
           setup_prover ()
             ~goal:"forall X, {foo X} -> {bar X}" ;

           induction [1] ;
           search () ;
           (* This may throw Failure("Proof completed") which
              indicates test failure *)
        );

      "Search should not find complex co-inductive hypothesis" >::
        (fun () ->
           setup_prover ()
             ~goal:"forall X, foo X -> bar X" ;

           List.iter (add_def Types.CoInductive)
             (parse_defs "bar X := bar X.") ;

           coinduction () ;
           search () ;
           (* This may throw Failure("Proof completed") which
              indicates test failure *)
        );

      "Search should find simple co-inductive hypothesis" >::
        (fun () ->
           setup_prover ()
             ~goal:"bar X" ;

           List.iter (add_def Types.CoInductive)
             (parse_defs "bar X := bar X.") ;

           assert_proof
             (fun () ->
                coinduction () ;
                search ())
        );

      "Apply should not work with IH as argument" >::
        (fun () ->
           setup_prover ()
             ~lemmas:[("lem", "(forall X, foo X -> bar X) -> baz")]
             ~goal:"forall X, foo X -> bar X" ;

           List.iter (add_def Types.Inductive)
             (parse_defs "foo X := foo X.") ;

           induction [1] ;
           assert_raises_any (fun () -> apply "lem" ["IH"] []) ;
        );

      "Apply should not work with CH as argument" >::
        (fun () ->
           setup_prover ()
             ~lemmas:[("lem", "(forall X, foo X -> bar X) -> baz")]
             ~goal:"forall X, foo X -> bar X" ;

           List.iter (add_def Types.CoInductive)
             (parse_defs "bar X := bar X.") ;

           coinduction () ;
           assert_raises_any (fun () -> apply "lem" ["CH"] []) ;
        );

      "Apply should not work with coinductively restricted argument" >::
        (fun () ->
           setup_prover ()
             ~lemmas:[("lem", "forall X, foo X -> bar X")]
             ~goal:"forall X, foo X + -> bar X" ;

           intros () ;
           assert_raises_any (fun () -> apply "lem" ["H1"] []) ;
        );

      "Case-analysis with nabla in the head, two in a row" >::
        (fun () ->
           setup_prover ()
             ~goal:"forall X Y, name X -> name Y -> \
                          (X = Y \\/ (X = Y -> false))" ;

           List.iter (add_def Types.Inductive)
             (parse_defs "nabla x, name x.") ;

           assert_proof
             (fun () ->
                intros () ;
                case "H1" ;
                assert_n_subgoals 1 ;

                case "H2" ;
                assert_n_subgoals 2 ;

                right () ;
                intros () ;
                case "H3" ;
                assert_n_subgoals 1 ;

                search ()
             )
        ) ;


    ]
