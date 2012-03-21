open OUnit
open Test_helper
open Term
open Metaterm
open Prover

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

           add_hyp (freshen "{eval A B}") ;
           case "H1" ;
           assert_bool "R should be added to variable list"
             (List.mem_assoc "R" sequent.vars)
        ) ;

      "Intros should raise over support" >::
        (fun () ->
           setup_prover ()
             ~goal:"forall L, rel1 n1 L" ;

           intros [] ;
           assert_goal "rel1 n1 (L n1)"
        ) ;

      "Intros on multiple nabla variables" >::
        (fun () ->
           setup_prover ()
             ~goal:"nabla (x:i) y, x = y" ;

           intros [] ;
           assert_goal "n1 = n2"
        ) ;

      "Assert test" >::
        (fun () ->
           setup_prover ()
             ~goal:"{a}" ;

           assert_hyp (parse_umetaterm "{b}") ;
           assert_n_subgoals 2 ;

           assert_pprint_equal "{b}" sequent.goal ;
           skip () ;
           assert_n_subgoals 1 ;

           assert_pprint_equal "{a}" sequent.goal ;
           match sequent.hyps with
             | [h] -> assert_pprint_equal "{b}" h.term
             | _ -> assert_failure "Expected one hypothesis"
        ) ;

      "Monotone test" >::
        (fun () ->
           setup_prover () ;

           add_hyp (freshen "{L, E |- conc A}*") ;

           monotone "H1" (parse_uterm "a :: b :: nil") ;

           assert_n_subgoals 2 ;
           assert_pprint_equal
             "forall X, member X (E :: L) -> member X (a :: b :: nil)"
             sequent.goal ;

           skip () ;
           assert_n_subgoals 1 ;
           match sequent.hyps with
             | [_; h] ->
                 assert_pprint_equal "{b, a |- conc A}*" h.term
             | _ -> assert_failure "Expected two hypotheses"
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
             | [h] ->
                 assert_pprint_equal "{A}" h.term ;
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
             | [h] ->
                 assert_pprint_equal "{A}" h.term ;
                 assert_pprint_equal "{B}" sequent.goal
             | _ -> assert_failure "Expected one hypothesis"
           end ;

           skip () ;
           begin match sequent.hyps with
             | [h1; h2] ->
                 assert_pprint_equal "{A}" h1.term ;
                 assert_pprint_equal "{B}" h2.term ;
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
             ~goal:"exists A, foo A" ;

           exists (parse_uterm "t1") ;

           assert_pprint_equal "foo t1" sequent.goal) ;

      "Obligations from apply should be added as subgoals" >::
        (fun () ->
           setup_prover ()
             ~goal:"baz B" ;

           add_hyp
             (freshen ("forall A, foo A -> bar A -> baz A")) ;
           add_hyp (freshen "foo B") ;

           assert_n_subgoals 1 ;

           apply "H1" ["H2"; "_"] [] ;
           assert_n_subgoals 2 ;
           assert_pprint_equal "bar B" sequent.goal ;

           skip () ;
           assert_n_subgoals 1 ;
           assert_pprint_equal "baz B" sequent.goal ;
        );

      "Apply should trigger case analysis" >::
        (fun () ->
           setup_prover () ;

           add_hyp (freshen "forall A, foo A -> bar A /\\ baz A") ;
           add_hyp (freshen "foo B") ;

           apply "H1" ["H2"] [] ;
           assert_pprint_equal "bar B" (get_hyp "H3") ;
           assert_pprint_equal "baz B" (get_hyp "H4") ;
        );

      "Cases should not consume fresh hyp names" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V, {typeof P V} -> {typeof P V}" ;

           intros [] ;
           case ~keep:true "H1" ;
           assert_n_subgoals 2 ;
           assert_string_list_equal ["H1"; "H2"]
             (List.map (fun h -> h.id) sequent.hyps) ;

           search () ;
           assert_n_subgoals 1 ;

           assert_string_list_equal
             ["H1"; "H2"; "H3"] (List.map (fun h -> h.id) sequent.hyps)
        ) ;

      "Skip should remove current subcase" >::
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V, {typeof P V} -> {typeof P V}" ;

           intros [] ;
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
                  intros [] ;
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
           intros [] ;
           assert_n_subgoals 1 ;

           save_undo_state () ;
           case "H1" ;
           assert_n_subgoals 2 ;

           undo () ;
           assert_n_subgoals 1 ;

           case "H1" ;
           assert_n_subgoals 2 ;
        ) ;

      "Inst should error on vacuous" >::
        (fun () ->
           setup_prover ()
             ~goal:"{b}" ;

           add_hyp (freshen "{a}") ;
           assert_raises (Failure("Vacuous instantiation"))
             (fun () -> inst "H1" [("n1", (parse_uterm "t1"))])
        ) ;

      "Proving OR" >::
        (fun () ->
           let clauses = parse_clauses "p1 t1. p1 t2. eq X X." in

             setup_prover ()
               ~clauses:clauses
               ~goal:"forall X, {p1 X} -> {eq X t1} \\/ {eq X t2}" ;

             assert_proof
               (fun () ->
                  induction [1] ;
                  intros [] ;

                  case "H1" ;
                  assert_n_subgoals 2 ;

                  search () ;
                  assert_n_subgoals 1 ;

                  search () ;
               )
        ) ;

      "OR on left side of arrow" >::
        (fun () ->
           let clauses = parse_clauses "p1 t1. p1 t2. eq X X." in

             setup_prover ()
               ~clauses:clauses
               ~goal:"forall X, {eq X t1} \\/ {eq X t2} -> {p1 X}" ;

             assert_proof
               (fun () ->
                  intros [] ;
                  case "H1" ;
                  assert_n_subgoals 2 ;

                  case "H2" ;
                  search () ;
                  assert_n_subgoals 1 ;

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
                  intros [] ;

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

      "Toplevel logic variable should produce error in apply" >::
        (fun () ->
           setup_prover () ;

           add_hyp (freshen "forall A, {a} -> bar A") ;
           add_hyp (freshen "{a}") ;

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
             ~goal:"forall X, {p1 X} -> {p2 X}" ;

           induction [1] ;
           search () ;
           (* This may throw Failure("Proof completed") which
              indicates test failure *)
        );

      "Search should not find complex co-inductive hypothesis" >::
        (fun () ->
           setup_prover ()
             ~goal:"forall X, foo X -> bar X" ;

           add_defs ["bar"] Abella_types.CoInductive
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

           add_defs ["bar"] Abella_types.CoInductive
             (parse_defs "bar X := bar X.") ;

           assert_proof
             (fun () ->
                coinduction () ;
                search ())
        );

      "Apply should not work with IH as argument" >::
        (fun () ->
           setup_prover ()
             ~lemmas:[("lem", "(forall X, foo X -> bar X) -> {a}")]
             ~goal:"forall X, foo X -> bar X" ;

           add_defs ["foo"] Abella_types.Inductive
             (parse_defs "foo X := foo X.") ;

           induction [1] ;
           assert_raises_any (fun () -> apply "lem" ["IH"] []) ;
        );

      "Apply should not work with CH as argument" >::
        (fun () ->
           setup_prover ()
             ~lemmas:[("lem", "(forall X, foo X -> bar X) -> {a}")]
             ~goal:"forall X, foo X -> bar X" ;

           add_defs ["bar"] Abella_types.CoInductive
             (parse_defs "bar X := bar X.") ;

           coinduction () ;
           assert_raises_any (fun () -> apply "lem" ["CH"] []) ;
        );

      "Apply should not work with coinductively restricted argument" >::
        (fun () ->
           setup_prover ()
             ~lemmas:[("lem", "forall X, foo X -> bar X")]
             ~goal:"forall X, foo X + -> bar X" ;

           intros [] ;
           assert_raises_any (fun () -> apply "lem" ["H1"] []) ;
        );

      "Case-analysis with nabla in the head, two in a row" >::
        (fun () ->
           setup_prover ()
             ~goal:"forall X Y, foo X -> foo Y -> \
                          (X = Y \\/ (X = Y -> false))" ;

           add_defs ["foo"] Abella_types.Inductive
             (parse_defs "nabla x, foo x.") ;

           assert_proof
             (fun () ->
                intros [] ;
                case "H1" ;
                assert_n_subgoals 1 ;

                case "H2" ;
                assert_n_subgoals 2 ;

                right () ;
                intros [] ;
                case "H3" ;
                assert_n_subgoals 1 ;

                search ()
             )
        ) ;

      "Induction within coinduction should fail" >::
        (fun () ->
           setup_prover ()
             ~goal:"forall X, foo X -> bar X" ;

           add_defs ["foo"] Abella_types.Inductive
             (parse_defs "foo X := foo X.") ;
           add_defs ["bar"] Abella_types.CoInductive
             (parse_defs "bar X := bar X.") ;

           coinduction () ;
           assert_raises (Failure "Induction within coinduction is not allowed")
             (fun () -> induction [1]) ;
        ) ;


      "Coinduction within induction should fail" >::
        (fun () ->
           setup_prover ()
             ~goal:"forall X, foo X -> bar X" ;

           add_defs ["foo"] Abella_types.Inductive
             (parse_defs "foo X := foo X.") ;
           add_defs ["bar"] Abella_types.CoInductive
             (parse_defs "bar X := bar X.") ;

           induction [1] ;
           assert_raises (Failure "Coinduction within induction is not allowed")
             coinduction ;
        ) ;

      "Huet's unification example" >::
        (fun () ->
           setup_prover ()
             ~goal:"forall F X, F (F X) = r1 (r1 t1) ->
                      (F = x1\\r1 (r1 t1)) \\/
                      (F = x1\\r1 x1 /\\ X = t1) \\/
                      (F = x1\\x1 /\\ X = r1 (r1 t1))" ;

           assert_proof
             (fun () ->
                intros [] ;
                case "H1" ;
                assert_n_subgoals 2 ;

                case "H2" ;
                assert_n_subgoals 3 ;

                case "H3" ;
                assert_n_subgoals 3 ;
                search () ;
                assert_n_subgoals 2 ;

                search () ;
                assert_n_subgoals 1 ;

                search () ;
             );
        ) ;

      "Split theorem" >::
        (fun () ->
           let t =
             parse_metaterm
               ("forall X, foo X -> " ^
                  "(forall Y, nabla Z, bar Y -> bar Z) /\\" ^
                  "(forall W, baz W)")
           in
             match split_theorem t with
               | [t1; t2] ->
                   assert_pprint_equal
                     "forall X Y, nabla Z, foo X -> bar Y -> bar Z" t1 ;
                   assert_pprint_equal
                     "forall X W, foo X -> baz W" t2 ;
               | ts -> assert_int_equal 2 (List.length ts)
        );

      "Split theorem (variable capture)" >::
        (fun () ->
           let t = parse_metaterm "forall X, foo X -> (forall X, bar X)" in
             assert_raises (Failure "Variable renaming required")
               (fun () -> split_theorem t)
        );

      "Split theorem (variable/constant capture)" >::
        (fun () ->
           let t = parse_metaterm "foo t1 -> (forall t1, bar t1)" in
             assert_raises (Failure "Variable renaming required")
               (fun () -> split_theorem t)
        );

      "Split with raising" >::
        (fun () ->
           let t =
             parse_metaterm
               ("forall X, nabla Z, rel1 X Z -> " ^
                  "(forall Y, nabla Z', rel2 Y Z') /\\" ^
                  "(forall W, foo W)")
           in
             match split_theorem t with
               | [t1; t2] ->
                   assert_pprint_equal
                     "forall X Y, nabla Z Z', rel1 X Z -> rel2 (Y Z) Z'" t1 ;
                   assert_pprint_equal
                     "forall X W, nabla Z, rel1 X Z -> foo (W Z)" t2 ;
               | ts -> assert_int_equal 2 (List.length ts)
        );

      "Split with raising (types test)" >::
        (fun () ->
           let t = parse_metaterm "nabla (Z1:tm) (Z2:ty), forall Y, foo Y" in
             match split_theorem t with
               | [t1] ->
                   assert_pprint_equal
                     "forall Y, nabla Z1 Z2, foo (Y Z1 Z2)" t1 ;
                   begin match t1 with
                     | Binding(Forall, [(y, ty)], _) ->
                         assert_ty_pprint_equal "tm -> ty -> i" ty ;
                     | _ -> assert false
                   end
               | ts -> assert_int_equal 1 (List.length ts)
        );

      "Split with raising and subordination" >::
        (fun () ->
           let t =
             parse_metaterm "nabla (x:sr_a) (y:sr_b), forall A B, sr_a_b A B"
           in
             match split_theorem t with
               | [t1] ->
                   assert_pprint_equal
                     "forall A B, nabla x y, sr_a_b (A x) (B x y)" t1 ;
               | ts -> assert_int_equal 1 (List.length ts)
        );

      "Intros should use subordination information" >::
        (fun () ->
             setup_prover ()
               ~goal:"nabla x y, forall X Y, sr_a_b x y -> sr_a_b X Y" ;

             intros [] ;
             assert_goal "sr_a_b (X n1) (Y n2 n1)" ;
        );

      "Should not be able to close built-in types" >::
        (fun () ->
           let should_not_close id =
             assert_raises (Failure ("Cannot close " ^ id))
               (fun () -> close_types [id])
           in
             should_not_close "o" ;
             should_not_close "olist" ;
             should_not_close "prop" ;
        );

    ]
