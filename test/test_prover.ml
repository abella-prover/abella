open Abella_lib
open Abella_types
open Test_helper
open Metaterm
open Prover

let keep id = Keep (id, [])
let remove id = Remove (id, [])

let search ?depth () =
  Prover.search ?depth ~witness:WMagic ~handle_witness:ignore ()

let assert_search_fails () =
  let outcome =
    try search () ; `found
    with Failure msg when msg = "Search failed" -> `failed
  in
  match outcome with
  | `failed -> ()
  | `found -> Alcotest.fail "Search unexpectedly found a proof"

let add_defs_for ids flavor clauses =
  let idtys =
    List.map (fun id -> (id, Typing.lookup_const !Typing.sign id)) ids
  in
  add_defs [] idtys flavor clauses

let split_theorem_bodies t =
  List.map snd (Prover.split_theorem ([], t))

let assert_n_subgoals n =
  if n <> 1 + List.length !subgoals then
    Alcotest.fail ("Expected " ^ (string_of_int n) ^ " subgoal(s), " ^
                      "but current proof state is,\n\n" ^ get_display ())

let assert_proof proof_function =
  try
    proof_function () ;
    Alcotest.fail ("Proof not completed,\n\n" ^ get_display ())
  with Prover.End_proof (`completed _) -> ()

let assert_goal goal =
  Alcotest.check Alcotest.string "strings differ" goal (metaterm_to_string sequent.goal)

let initial_bind_state = Term.get_bind_state ()
let initial_sequent = copy_sequent ()
let initial_clauses = !clauses
let initial_defs_table = Hashtbl.copy defs_table

let setup_prover ?clauses:(clauses=[])
    ?goal:(goal="") ?lemmas:(lemmas=[]) () =
  State.Undo.set_enabled true ;
  State.Undo.reset () ;
  full_reset_prover initial_bind_state initial_sequent
    initial_clauses initial_defs_table () ;
  Hashtbl.reset Prover.lemmas ;
  Hashtbl.reset Prover.lemma_tags ;
  add_clauses clauses ;
  if goal <> "" then Prover.sequent.goal <- freshen goal ;
  List.iter
    (fun (name, body) -> ignore (add_lemma name [] (parse_metaterm body)))
    lemmas

let tests =
  suite "Prover" [
      test_case "New variables added to context"
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses ;

           add_hyp (freshen "{eval A B}") ;
           case (remove "H1") ;
           Alcotest.check Alcotest.bool
             "R should be added to variable list" true
             (List.mem_assoc "R" sequent.vars)
        ) ;

      test_case "Intros should raise over support"
        (fun () ->
           setup_prover ()
             ~goal:"forall L, rel1 n1 L" ;

           intros [] ;
           assert_goal "rel1 n1 (L n1)"
        ) ;

      test_case "Intros on multiple nabla variables"
        (fun () ->
           setup_prover ()
             ~goal:"nabla (x:i) y, x = y" ;

           intros [] ;
           assert_goal "n1 = n2"
        ) ;

      test_case "Assert test"
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
             | _ -> Alcotest.fail "Expected one hypothesis"
        ) ;

      test_case "Monotone test"
        (fun () ->
           setup_prover () ;

           add_hyp (freshen "{L, E |- conc A}*") ;

           monotone (keep "H1") (parse_uterm "a :: b :: nil") ;

           assert_n_subgoals 2 ;
           assert_pprint_equal
             "forall X, member X (E :: L) -> member X (a :: b :: nil)"
             sequent.goal ;

           skip () ;
           assert_n_subgoals 1 ;
           match sequent.hyps with
             | [_; h] ->
                 assert_pprint_equal "{b, a |- conc A}*" h.term
             | _ -> Alcotest.fail "Expected two hypotheses"
        ) ;

      test_case "Split test"
        (fun () ->
           setup_prover ()
             ~goal:"{A} /\\ {B}" ;

           split false ;
           assert_n_subgoals 2 ;

           assert_pprint_equal "{A}" sequent.goal ;

           skip () ;
           match sequent.hyps with
             | [] -> assert_pprint_equal "{B}" sequent.goal
             | _ -> Alcotest.fail "Expected no hypotheses"
        ) ;

      test_case "SplitStar test"
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
             | _ -> Alcotest.fail "Expected one hypothesis"
        ) ;

      test_case "Split many test"
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

      test_case "SplitStar many test"
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
             | _ -> Alcotest.fail "Expected one hypothesis"
           end ;

           skip () ;
           begin match sequent.hyps with
             | [h1; h2] ->
                 assert_pprint_equal "{A}" h1.term ;
                 assert_pprint_equal "{B}" h2.term ;
                 assert_pprint_equal "{C}" sequent.goal
             | _ -> Alcotest.fail "Expected two hypotheses"
           end
        ) ;

      test_case "Needless split"
        (fun () ->
           setup_prover ()
             ~goal:"{A}" ;

           Alcotest.check_raises "Needless use of split"
             (Failure "Needless use of split")
             (fun () -> ignore (split false))
        ) ;

      test_case "Exists test"
        (fun () ->
           setup_prover ()
             ~goal:"exists A, foo A" ;

           exists (ETerm (parse_uterm "t1")) ;

           assert_pprint_equal "foo t1" sequent.goal) ;

      test_case "Obligations from apply should be added as subgoals"
        (fun () ->
           setup_prover ()
             ~goal:"baz B" ;

           add_hyp
             (freshen ("forall A, foo A -> bar A -> baz A")) ;
           add_hyp (freshen "foo B") ;

           assert_n_subgoals 1 ;

           apply (keep "H1") (List.map keep ["H2"; "_"]) [] ;
           assert_n_subgoals 2 ;
           assert_pprint_equal "bar B" sequent.goal ;

           skip () ;
           assert_n_subgoals 1 ;
           assert_pprint_equal "baz B" sequent.goal ;
        );

      test_case "Apply should trigger case analysis"
        (fun () ->
           setup_prover () ;

           add_hyp (freshen "forall A, foo A -> bar A /\\ baz A") ;
           add_hyp (freshen "foo B") ;

           apply (keep "H1") (List.map keep ["H2"]) [] ;
           assert_pprint_equal "bar B" (get_hyp "H3") ;
           assert_pprint_equal "baz B" (get_hyp "H4") ;
        );

      test_case "Cases should not consume fresh hyp names"
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V, {typeof P V} -> {typeof P V}" ;

           intros [] ;
           case (keep "H1") ;
           assert_n_subgoals 2 ;
           Alcotest.check (Alcotest.list Alcotest.string) "string lists differ" ["H1"; "H2"]
             (List.map (fun h -> h.id) sequent.hyps) ;

           search () ;
           assert_n_subgoals 1 ;

           Alcotest.check (Alcotest.list Alcotest.string) "hypotheses"
             ["H1"; "H2"; "H3"] (List.map (fun h -> h.id) sequent.hyps)
        ) ;

      test_case "Skip should remove current subcase"
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V, {typeof P V} -> {typeof P V}" ;

           intros [] ;
           case (remove "H1") ;
           assert_n_subgoals 2 ;

           skip () ;
           assert_n_subgoals 1 ;
        ) ;

      test_case "Add example (lemmas)"
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
                  case (remove "H2") ;
                  assert_n_subgoals 2 ;

                  apply (keep "base") (List.map keep ["H1"]) [] ;
                  search () ;
                  assert_n_subgoals 1 ;

                  apply (keep "IH") (List.map keep ["H1"; "H3"]) [] ;
                  apply (keep "step") (List.map keep ["H4"]) [] ;
                  search () ;
               )
        ) ;

      test_case "Undo should restore previous save state"
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V T, {eval P V} -> {typeof P T} -> {typeof V T}" ;

           induction [1] ;
           intros [] ;
           assert_n_subgoals 1 ;

           State.Undo.push () ;
           case (remove "H1") ;
           assert_n_subgoals 2 ;

           State.Undo.undo () ;
           assert_n_subgoals 1 ;

           case (remove "H1") ;
           assert_n_subgoals 2 ;
        ) ;

      test_case "Inst should error on vacuous"
        (fun () ->
           setup_prover ()
             ~goal:"{b}" ;

           add_hyp (freshen "{a}") ;
           Alcotest.match_raises "Vacuous instantiation"
             (function
               | Failure msg ->
                   String.starts_with ~prefix:"Nominal constant n1" msg
               | _ -> false)
             (fun () -> ignore (inst (keep "H1") [("n1", (parse_uterm "t1"))]))
        ) ;

      test_case "Proving OR"
        (fun () ->
           let clauses = parse_clauses "p1 t1. p1 t2. eq X X." in

             setup_prover ()
               ~clauses:clauses
               ~goal:"forall X, {p1 X} -> {eq X t1} \\/ {eq X t2}" ;

             assert_proof
               (fun () ->
                  induction [1] ;
                  intros [] ;

                  case (remove "H1") ;
                  assert_n_subgoals 2 ;

                  search () ;
                  assert_n_subgoals 1 ;

                  search () ;
               )
        ) ;

      test_case "OR on left side of arrow"
        (fun () ->
           let clauses = parse_clauses "p1 t1. p1 t2. eq X X." in

             setup_prover ()
               ~clauses:clauses
               ~goal:"forall X, {eq X t1} \\/ {eq X t2} -> {p1 X}" ;

             assert_proof
               (fun () ->
                  intros [] ;
                  case (remove "H1") ;
                  assert_n_subgoals 2 ;

                  case (remove "H2") ;
                  search () ;
                  assert_n_subgoals 1 ;

                  case (remove "H2") ;
                  search () ;
               )
        ) ;

      test_case "Using IH with OR"
        (fun () ->
           let clauses = parse_clauses
             ("nat z. nat (s X) :- nat X. " ^
                "even z. even (s X) :- odd X. " ^
                "odd (s z). odd (s X) :- even X.") in

             setup_prover ()
               ~clauses:clauses
               ~goal:"forall X, {nat X} -> {even X} \\/ {odd X}" ;

             assert_proof
               (fun () ->
                  induction [1] ;
                  intros [] ;

                  case (remove "H1") ;
                  assert_n_subgoals 2 ;

                  search () ;
                  assert_n_subgoals 1 ;

                  apply (keep "IH") (List.map keep ["H2"]) [] ;
                  case (remove "H3") ;
                  assert_n_subgoals 2 ;

                  search () ;
                  assert_n_subgoals 1 ;

                  search () ;
               )
        ) ;

      test_case "Toplevel logic variable should produce error in apply"
        (fun () ->
           setup_prover () ;

           add_hyp (freshen "forall A, {a} -> bar A") ;
           add_hyp (freshen "{a}") ;

           try
             apply (keep "H1") (List.map keep ["H2"]) [] ;
             Alcotest.fail ("Logic variable did not produce error\n\n" ^
                               get_display ())
           with
             | Failure msg
               when String.starts_with ~prefix:"Found logic variable at toplevel"
                      msg -> ()
        ) ;

      test_case "Search should not find the inductive hypothesis"
        (fun () ->
           setup_prover ()
             ~goal:"forall X, {p1 X} -> {p2 X}" ;

           induction [1] ;
           assert_search_fails ()
        );

      test_case "Search should not find complex co-inductive hypothesis"
        (fun () ->
           setup_prover ()
             ~goal:"forall X, foo X -> bar X" ;

           add_defs_for ["bar"] Abella_types.CoInductive
             (parse_defs "bar X := bar X.") ;

           coinduction () ;
           assert_search_fails ()
        );

      test_case "Search should find simple co-inductive hypothesis"
        (fun () ->
           setup_prover ()
             ~goal:"bar X" ;

           add_defs_for ["bar"] Abella_types.CoInductive
             (parse_defs "bar X := bar X.") ;

           assert_proof
             (fun () ->
                coinduction () ;
                search ())
        );

      test_case "Apply should not work with IH as argument"
        (fun () ->
           setup_prover ()
             ~lemmas:[("lem", "(forall X, foo X -> bar X) -> {a}")]
             ~goal:"forall X, foo X -> bar X" ;

           add_defs_for ["foo"] Abella_types.Inductive
             (parse_defs "foo X := foo X.") ;

           induction [1] ;
           Alcotest.match_raises "expected exception" (fun _ -> true)
             (fun () -> ignore (apply (keep "lem") (List.map keep ["IH"]) [])) ;
        );

      test_case "Apply should not work with CH as argument"
        (fun () ->
           setup_prover ()
             ~lemmas:[("lem", "(forall X, foo X -> bar X) -> {a}")]
             ~goal:"forall X, foo X -> bar X" ;

           add_defs_for ["bar"] Abella_types.CoInductive
             (parse_defs "bar X := bar X.") ;

           coinduction () ;
           Alcotest.match_raises "expected exception" (fun _ -> true)
             (fun () -> ignore (apply (keep "lem") (List.map keep ["CH"]) [])) ;
        );

      test_case "Apply should not work with coinductively restricted argument"
        (fun () ->
           setup_prover ()
             ~lemmas:[("lem", "forall X, foo X -> bar X")]
             ~goal:"forall X, foo X + -> bar X" ;

           intros [] ;
           Alcotest.match_raises "expected exception" (fun _ -> true)
             (fun () -> ignore (apply (keep "lem") (List.map keep ["H1"]) [])) ;
        );

      test_case "Case-analysis with nabla in the head, two in a row"
        (fun () ->
           setup_prover ()
             ~goal:"forall X Y, foo X -> foo Y -> \
                          (X = Y \\/ (X = Y -> false))" ;

           add_defs_for ["foo"] Abella_types.Inductive
             (parse_defs "nabla x, foo x.") ;

           assert_proof
             (fun () ->
                intros [] ;
                case (remove "H1") ;
                assert_n_subgoals 1 ;

                case (remove "H2") ;
                assert_n_subgoals 2 ;

                right () ;
                intros [] ;
                case (remove "H3") ;
                assert_n_subgoals 1 ;

                search ()
             )
        ) ;

      test_case "Induction within coinduction should fail"
        (fun () ->
           setup_prover ()
             ~goal:"forall X, foo X -> bar X" ;

           add_defs_for ["foo"] Abella_types.Inductive
             (parse_defs "foo X := foo X.") ;
           add_defs_for ["bar"] Abella_types.CoInductive
             (parse_defs "bar X := bar X.") ;

           coinduction () ;
           Alcotest.check_raises
             "Induction within coinduction is not allowed"
             (Failure "Induction within coinduction is not allowed")
             (fun () -> ignore (induction [1])) ;
        ) ;


      test_case "Coinduction within induction should fail"
        (fun () ->
           setup_prover ()
             ~goal:"forall X, foo X -> bar X" ;

           add_defs_for ["foo"] Abella_types.Inductive
             (parse_defs "foo X := foo X.") ;
           add_defs_for ["bar"] Abella_types.CoInductive
             (parse_defs "bar X := bar X.") ;

           induction [1] ;
           Alcotest.check_raises
             "Coinduction within induction is not allowed"
             (Failure "Coinduction within induction is not allowed")
             (fun () -> ignore (coinduction ())) ;
        ) ;

      test_case "Huet's unification example"
        (fun () ->
           setup_prover ()
             ~goal:"forall F X, F (F X) = r1 (r1 t1) ->
                      (F = x1\\r1 (r1 t1)) \\/
                      (F = x1\\r1 x1 /\\ X = t1) \\/
                      (F = x1\\x1 /\\ X = r1 (r1 t1))" ;

           assert_proof
             (fun () ->
                intros [] ;
                case (remove "H1") ;
                assert_n_subgoals 2 ;

                case (remove "H2") ;
                assert_n_subgoals 3 ;

                case (remove "H3") ;
                assert_n_subgoals 3 ;
                search () ;
                assert_n_subgoals 2 ;

                search () ;
                assert_n_subgoals 1 ;

                search () ;
             );
        ) ;

      test_case "Split theorem"
        (fun () ->
           let t =
             parse_metaterm
               ("forall X, foo X -> " ^
                  "(forall Y, nabla Z, bar Y -> bar Z) /\\" ^
                  "(forall W, baz W)")
           in
             match split_theorem_bodies t with
               | [t1; t2] ->
                   assert_pprint_equal
                     "forall X Y, nabla Z, foo X -> bar Y -> bar Z" t1 ;
                   assert_pprint_equal
                     "forall X W, foo X -> baz W" t2 ;
               | ts -> Alcotest.check Alcotest.int "ints differ" 2 (List.length ts)
        );

      test_case "Split with raising"
        (fun () ->
           let t =
             parse_metaterm
               ("forall X, nabla Z, rel1 X Z -> " ^
                  "(forall Y, nabla Z', rel2 Y Z') /\\" ^
                  "(forall W, foo W)")
           in
             match split_theorem_bodies t with
               | [t1; t2] ->
                   assert_pprint_equal
                     "forall X Y, nabla Z Z', rel1 X Z -> rel2 (Y Z) Z'" t1 ;
                   assert_pprint_equal
                     "forall X W, nabla Z, rel1 X Z -> foo (W Z)" t2 ;
               | ts -> Alcotest.check Alcotest.int "ints differ" 2 (List.length ts)
        );

      test_case "Split with raising (types test)"
        (fun () ->
           let t = parse_metaterm "nabla (Z1:tm) (Z2:ty), forall Y, foo Y" in
             match split_theorem_bodies t with
               | [t1] ->
                   assert_pprint_equal
                     "forall Y, nabla Z1 Z2, foo (Y Z1 Z2)" t1 ;
                   begin match t1 with
                     | Binding(Forall, [(_, ty)], _) ->
                         assert_ty_pprint_equal "tm -> ty -> i" ty ;
                     | _ -> assert false
                   end
               | ts -> Alcotest.check Alcotest.int "ints differ" 1 (List.length ts)
        );

      test_case "Split with raising and subordination"
        (fun () ->
           let t =
             parse_metaterm "nabla (x:sr_a) (y:sr_b), forall A B, sr_a_b A B"
           in
             match split_theorem_bodies t with
               | [t1] ->
                   assert_pprint_equal
                     "forall A B, nabla x y, sr_a_b (A x) (B x y)" t1 ;
               | ts -> Alcotest.check Alcotest.int "ints differ" 1 (List.length ts)
        );

      test_case "Intros should use subordination information"
        (fun () ->
             setup_prover ()
               ~goal:"nabla x y, forall X Y, sr_a_b x y -> sr_a_b X Y" ;

             intros [] ;
             assert_goal "sr_a_b (X n1) (Y n2 n1)" ;
        );

      test_case "Should not be able to close built-in types"
        (fun () ->
           let should_not_close name msg aty =
             Alcotest.check_raises
               ("Cannot close " ^ name)
               (Failure ("Cannot close " ^ msg))
               (fun () ->
                  ignore (close_types !Typing.sign !Prover.clauses [aty]))
           in
             should_not_close "o" "o" Term.oaty ;
             should_not_close "olist" "list o" Term.olistaty ;
             should_not_close "prop" "prop" Term.propaty ;
        );

      test_case "Saturate should add consequences as hypotheses"
        (fun () ->
           setup_prover ()
             ~goal:"false"
             ~lemmas:[("p12", "forall X, foo X -> bar X")] ;

           add_hyp (freshen "foo t1") ;
           saturate ["p12"] ;

           assert_n_subgoals 1 ;
           Alcotest.check (Alcotest.list Alcotest.string) "hypotheses"
             ["H1"; "H2"] (List.map (fun h -> h.id) sequent.hyps) ;
           assert_pprint_equal "bar t1" (get_hyp "H2")
        ) ;

      test_case "Saturate should default depth to the number of lemmas"
        (fun () ->
           setup_prover ()
             ~goal:"false"
             ~lemmas:[
               ("p12", "forall X, foo X -> bar X") ;
               ("p23", "forall X, bar X -> baz X")] ;

           add_hyp (freshen "foo t1") ;
           saturate ["p12"; "p23"] ;

           assert_n_subgoals 1 ;
           Alcotest.check (Alcotest.list Alcotest.string) "hypotheses"
             ["H1"; "H2"; "H3"] (List.map (fun h -> h.id) sequent.hyps) ;
           assert_pprint_equal "bar t1" (get_hyp "H2") ;
           assert_pprint_equal "baz t1" (get_hyp "H3")
        ) ;

      test_case "Saturate should respect an explicit depth"
        (fun () ->
           setup_prover ()
             ~goal:"false"
             ~lemmas:[
               ("p12", "forall X, foo X -> bar X") ;
               ("p23", "forall X, bar X -> baz X")] ;

           add_hyp (freshen "foo t1") ;
           saturate ~depth:1 ["p12"; "p23"] ;

           assert_n_subgoals 1 ;
           Alcotest.check (Alcotest.list Alcotest.string) "hypotheses"
             ["H1"; "H2"] (List.map (fun h -> h.id) sequent.hyps) ;
           assert_pprint_equal "bar t1" (get_hyp "H2")
        ) ;

      test_case "Saturate should use hypotheses as lemmas"
        (fun () ->
           setup_prover () ~goal:"false" ;

           add_hyp (freshen "forall X, foo X -> bar X") ;
           add_hyp (freshen "foo t1") ;
           saturate ["H1"] ;

           assert_n_subgoals 1 ;
           Alcotest.check (Alcotest.list Alcotest.string) "hypotheses"
             ["H1"; "H2"; "H3"] (List.map (fun h -> h.id) sequent.hyps) ;
           assert_pprint_equal "bar t1" (get_hyp "H3")
        ) ;

      test_case "Saturate should not release non-ground formulas"
        (fun () ->
           setup_prover ()
             ~goal:"false"
             ~lemmas:[("ng", "forall X, bar X")] ;

           saturate ["ng"] ;

           assert_n_subgoals 1 ;
           Alcotest.check (Alcotest.list Alcotest.string) "hypotheses"
             [] (List.map (fun h -> h.id) sequent.hyps)
        ) ;

      test_case "Clear should remove duplicate hypotheses"
        (fun () ->
           setup_prover () ;

           add_hyp (freshen "foo t1") ;
           add_hyp (freshen "foo t1") ;
           add_hyp (freshen "{a}") ;
           add_hyp (freshen "{a}") ;

           clear_duplicates () ;

           Alcotest.check (Alcotest.list Alcotest.string) "hypotheses"
             ["H1"; "H3"; "H4"] (List.map (fun h -> h.id) sequent.hyps)
        ) ;

      test_case "Skip should mark the proof as unfinished"
        (fun () ->
           setup_prover () ~goal:"true /\\ true" ;

           split false ;
           start_proof () ;
           skip () ;

           begin
             try
               search () ;
               Alcotest.fail ("Proof not completed,\n\n" ^ get_display ())
             with
             | End_proof (`completed fin) ->
                 Alcotest.check Alcotest.bool
                   "proof should be unfinished" true (fin = Unfinished)
           end
        ) ;

      test_case "Start proof should reset the skipped status"
        (fun () ->
           setup_prover () ~goal:"true" ;

           start_proof () ;

           begin
             try
               search () ;
               Alcotest.fail ("Proof not completed,\n\n" ^ get_display ())
             with
             | End_proof (`completed fin) ->
                 Alcotest.check Alcotest.bool
                   "proof should be finished" true (fin = Finished)
           end
        ) ;

      test_case "Lemma tags should be tracked"
        (fun () ->
           setup_prover ()
             ~lemmas:[("done", "true")] ;

           Alcotest.check Alcotest.bool "default tag should be finished"
             true (get_lemma_tag "done" = Finished) ;

           ignore (add_lemma ~fin:Unfinished "skipped" []
                     (parse_metaterm "true")) ;
           Alcotest.check Alcotest.bool "explicit tag should be kept"
             true (get_lemma_tag "skipped" = Unfinished) ;

           Alcotest.check_raises "unknown lemma should fail"
             (Failure "Could not find theorem named \"unknown\"")
             (fun () -> ignore (get_lemma_tag "unknown"))
        ) ;

      test_case "State JSON should describe the sequent"
        (fun () ->
           setup_prover () ~goal:"{a}" ;

           add_hyp (freshen "{b}") ;
           let fields =
             match state_json () with
             | `Assoc fields -> fields
             | _ -> Alcotest.fail "State JSON should be an object"
           in
           let field name =
             try List.assoc name fields
             with Not_found -> Alcotest.fail ("Missing field " ^ name)
           in
           let string_field name =
             match field name with
             | `String s -> s
             | _ -> Alcotest.fail ("Field " ^ name ^ " should be a string")
           in
           let int_field name =
             match field name with
             | `Int n -> n
             | _ -> Alcotest.fail ("Field " ^ name ^ " should be an integer")
           in
           Alcotest.check Alcotest.string "goal differs" "{a}"
             (string_field "goal") ;
           Alcotest.check Alcotest.string "name differs" ""
             (string_field "name") ;
           Alcotest.check Alcotest.int "subgoal count differs" 0
             (int_field "more") ;
           Alcotest.check Alcotest.string "hyps differ" {|[["H1","{b}"]]|}
             (Extensions.Json.to_string (field "hyps")) ;
           Alcotest.check Alcotest.string "vars differ" "[]"
             (Extensions.Json.to_string (field "vars"))
        ) ;

      test_case "State JSON should describe subgoals"
        (fun () ->
           setup_prover () ~goal:"{a} /\\ {b}" ;

           split false ;

           match state_json () with
           | `Assoc fields ->
               let string_field name =
                 match List.assoc name fields with
                 | `String s -> s
                 | _ ->
                     Alcotest.fail (name ^ " should be a string")
               in
               let int_field name =
                 match List.assoc name fields with
                 | `Int n -> n
                 | _ ->
                     Alcotest.fail (name ^ " should be an integer")
               in
               Alcotest.check Alcotest.string "name differs" "1"
                 (string_field "name") ;
               Alcotest.check Alcotest.int "subgoal count differs" 1
                 (int_field "more") ;
               Alcotest.check Alcotest.string "goal differs" "{a}"
                 (string_field "goal")
           | _ -> Alcotest.fail "State JSON should be an object"
        ) ;

      test_case "Remove globals should forget lemmas and definitions"
        (fun () ->
           setup_prover () ;

           add_defs_for ["foo"] Abella_types.Inductive
             (parse_defs "foo X := foo X.") ;
           ignore (add_lemma "foo_lem" [] (parse_metaterm "foo t1")) ;

           remove_globals ["foo"; "foo_lem"] ;

           Alcotest.check Alcotest.bool "definition should be removed" false
             (Hashtbl.mem defs_table "foo") ;
           Alcotest.check_raises "lemma should be removed"
             (Failure "Could not find theorem named \"foo_lem\"")
             (fun () -> ignore (get_lemma_tag "foo_lem"))
        ) ;

      test_case "Backchain should discharge obligations by search"
        (fun () ->
           setup_prover () ~goal:"baz B" ;

           add_hyp (freshen "forall A, foo A -> baz A") ;
           add_hyp (freshen "foo B") ;

           assert_proof
             (fun () -> backchain (keep "H1") [])
        ) ;

      test_case "Backchain should leave unsolved obligations as subgoals"
        (fun () ->
           setup_prover () ~goal:"baz B" ;

           add_hyp (freshen "forall A, foo A -> baz A") ;

           backchain (keep "H1") [] ;

           assert_n_subgoals 1 ;
           assert_goal "foo B"
        ) ;

      test_case "Cut should add the cut formula as a hypothesis"
        (fun () ->
           setup_prover () ~goal:"{b}" ;

           add_hyp (freshen "{a |- b}") ;
           add_hyp (freshen "{a}") ;

           cut (keep "H1") (keep "H2") ;

           assert_pprint_equal "{b}" (get_hyp "H3")
        ) ;

      test_case "Search cut should remove provable context items"
        (fun () ->
           setup_prover ()
             ~clauses:(parse_clauses "p1 t1.")
             ~goal:"{a}" ;

           add_hyp (freshen "{p1 t1, p2 t1 |- a}") ;
           search_cut (keep "H1") ;

           assert_pprint_equal "{p2 t1 |- a}" (get_hyp "H2")
        ) ;

      test_case "Cut from should replace the cut term with the context"
        (fun () ->
           setup_prover () ~goal:"{c}" ;

           add_hyp (freshen "{a, b |- c}") ;
           add_hyp (freshen "{d |- b}") ;

           cut_from (keep "H1") (keep "H2") (parse_uterm "b") ;

           assert_pprint_equal "{d, a |- c}" (get_hyp "H3")
        ) ;

      test_case "Abbrev should apply to several hypotheses"
        (fun () ->
           setup_prover () ;

           add_hyp (freshen "{a}") ;
           add_hyp (freshen "{b}") ;

           abbrev (Term.Iset.of_list ["H1"; "H2"]) "both" ;
           Alcotest.check Alcotest.bool "both should be abbreviated" true
             (List.for_all
                (fun h -> h.abbrev = Some "both") sequent.hyps) ;

           unabbrev (Term.Iset.of_list ["H1"]) ;
           match sequent.hyps with
           | [h1; h2] ->
               Alcotest.check Alcotest.bool "H1 should be unabbreviated"
                 true (h1.abbrev = None) ;
               Alcotest.check Alcotest.bool "H2 should stay abbreviated"
                 true (h2.abbrev = Some "both")
           | _ -> Alcotest.fail "Expected two hypotheses"
        ) ;

      test_case "Monotone should honor a hypothesis name hint"
        (fun () ->
           setup_prover () ;

           add_hyp (freshen "{L, E |- conc A}*") ;

           monotone ~name:"M" (keep "H1")
             (parse_uterm "a :: b :: nil") ;

           assert_n_subgoals 2 ;
           skip () ;
           assert_n_subgoals 1 ;
           match sequent.hyps with
           | [_; h] ->
               Alcotest.check Alcotest.string "hypothesis name differs"
                 "M" h.id ;
               assert_pprint_equal "{b, a |- conc A}*" h.term
           | _ -> Alcotest.fail "Expected two hypotheses"
        ) ;

      test_case "Apply should respect an explicit search depth"
        (fun () ->
           setup_prover ()
             ~clauses:(parse_clauses "foo t1.")
             ~goal:"bar t1" ;

           add_hyp (freshen "forall X, foo X -> bar X") ;

           apply ~depth:0 (keep "H1") (List.map keep ["_"])
             [("X", parse_uterm "t1")] ;

           assert_n_subgoals 2 ;
           assert_goal "foo t1"
        ) ;

      test_case "Clear should extrude a hypothesis into the goal"
        (fun () ->
           setup_prover () ~goal:"{b}" ;

           add_hyp (freshen "{a}") ;

           clear Clear_extro ["H1"] ;

           Alcotest.check (Alcotest.list Alcotest.string) "hypotheses"
             [] (List.map (fun h -> h.id) sequent.hyps) ;
           assert_goal "{a} -> {b}"
        ) ;

      test_case "Split theorem should allow repeated binder names"
        (fun () ->
           let t =
             parse_metaterm
               ("(forall (A:i), A = A) -> " ^
                  "(forall (A:i), A = A) /\\ " ^
                  "(forall (A:i), A = A)")
           in
           match split_theorem_bodies t with
           | [t1; t2] ->
               assert_pprint_equal
                 "forall A, (forall A, A = A) -> A = A" t1 ;
               assert_pprint_equal
                 "forall A, (forall A, A = A) -> A = A" t2
           | ts ->
               Alcotest.check Alcotest.int "ints differ" 2
                 (List.length ts)
        ) ;

      test_case "Search should not lower eigenvariable timestamps"
        (fun () ->
           setup_prover ()
             ~goal:"forall (v:i), exists y, \
                      forall u, v = r1 u -> y = u" ;

           assert_search_fails ()
        ) ;

      test_case "Apply should avoid capture of sequent variables"
        (fun () ->
           setup_prover ()
             ~goal:"forall (E':i), true"
             ~lemmas:[
               ("foo",
                "forall (E:i), (E = E) -> \
                 (forall E', E = E' -> true) -> true")] ;

           assert_proof
             (fun () ->
                start_proof () ;
                intros [] ;
                assert_hyp (parse_umetaterm "E' = E'") ;
                assert_hyp (parse_umetaterm "forall Y, E' = Y -> true") ;
                apply (keep "foo") (List.map keep ["H1"; "_"]) [] ;
                apply (keep "foo") (List.map keep ["_"; "H2"]) [] ;
                apply (keep "foo") (List.map keep ["H1"; "H2"]) [] ;
                search ())
        ) ;

      test_case "Case analysis should preserve the lambda prefix"
        (fun () ->
           process_top_command "Kind expr155 type." ;
           process_top_command
             "Type mu155 ((expr155 -> expr155) -> expr155) -> \
              expr155." ;
           process_top_command
             "Type foo155 expr155 -> expr155 -> prop." ;
           setup_prover ()
             ~goal:"forall E E', nabla (x:expr155), \
                      foo155 (E x) (E' x) -> true" ;
           add_defs_for ["foo155"] Abella_types.Inductive
             (parse_defs "foo155 (mu155 k\\ E k) \
                          (mu155 k_\\ E (o\\ o)).") ;
           intros [] ;
           case (keep "H1") ;
           assert_n_subgoals 1 ;
           assert_pprint_equal
             "foo155 (mu155 (x1\\E1 n1 x1)) (mu155 (x1\\E1 n1 x2\\x2))"
             (get_hyp "H1")
        ) ;

    ]
