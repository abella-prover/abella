open Abella_lib
open Types
open Test_helper
open Metaterm
open Prover

let keep id = Keep (id, [])
let remove id = Remove (id, [])
let no_hints = { hspec_vars = [] ; hspec_hyps = [] }
let hyp_hint name =
  Some [{ hspec_vars = [] ; hspec_hyps = [User_name name] }]
let user_alt vars hyps =
  { hspec_vars = List.map (fun name -> User_name name) vars ;
    hspec_hyps = List.map (fun name -> User_name name) hyps }


(* Explicit proof-state harness over the immutable engine *)

let placeholder_goal = Metaterm.termobj (Term.const "placeholder" Term.propty)

let st : proof_state ref =
  State.rref (start_proof (empty_sequent placeholder_goal))

let or_fail to_string = function
  | Result.Ok x -> x
  | Result.Error e -> failwith (to_string e)

let focused () =
  match (!st).focused with
  | Some sq -> activate_sequent sq
  | None -> begin
      match (!st).bullets with
      | [] -> Alcotest.fail "expected a focused subgoal"
      | f :: _ ->
          failwith (string_of_bullet_error (No_focused_subgoal f.bullet))
    end

let normalize_focused_state s =
  match s.focused with
  | None -> s
  | Some sq ->
      { s with focused = Some (normalize_sequent (activate_sequent sq)) }

let install_updated sq' = st := { !st with focused = Some sq' }

let install_branched sq subs =
  let s = push_subgoals { !st with focused = Some sq } subs in
  let s =
    match s.focused with
    | Some _ -> s
    | None -> next_subgoal s
  in
  st := normalize_focused_state s

let run_updated f = install_updated (f (focused ()))

let run_branched f =
  let sq = focused () in
  install_branched sq (f sq)

let run_delayed f =
  let sq = focused () in
  begin match f sq with
  | Solved sq' -> install_updated sq'
  | Delayed gs -> install_branched sq gs
  end

let search ?depth () =
  run_branched (fun sq ->
      or_fail string_of_search_error
        (Prover.search sq ?depth ~witness:WMagic ~handle_witness:ignore ()))

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
  Prover.add_defs [] idtys flavor clauses

let split_theorem_bodies t =
  List.map snd (Prover.split_theorem ([], t))

let assert_n_subgoals n =
  let s = !st in
  let m =
    (match s.focused with None -> 0 | Some _ -> 1)
    + List.length s.pending
  in
  if n <> m then
    Alcotest.fail ("Expected " ^ (string_of_int n) ^ " subgoal(s), " ^
                      "but current proof state is,\n\n" ^
                        Prover.get_display s)

let assert_proof proof_function =
  proof_function () ;
  if not (is_completed !st) then
    Alcotest.fail ("Proof not completed,\n\n" ^ Prover.get_display !st)

let assert_goal goal =
  Alcotest.check Alcotest.string "strings differ" goal
    (metaterm_to_string (focused ()).goal)

let get_display () = Prover.get_display !st
let state_json () = Prover.state_json !st
let is_focused () = Option.is_some (!st).focused
let expected_bullet () =
  match (!st).bullets with
  | [] -> None
  | f :: _ -> Some f.bullet

let get_hyp name =
  match Prover.get_hyp (focused ()) name with
  | Some t -> t
  | None -> Alcotest.fail ("no such hypothesis: " ^ name)

let add_hyp ?name term =
  install_updated (Prover.add_hyp (focused ()) ?name term)
let case ?hint h =
  run_branched (fun sq ->
      or_fail string_of_case_error (Prover.case sq ?hint h))
let intros alt =
  run_updated (fun sq ->
      match Prover.intros sq alt with
      | Result.Ok sq' -> sq'
      | Result.Error (Intros_rename e) ->
          failwith (string_of_rename_hint_error e))
let split propagate =
  run_branched (fun sq ->
      or_fail string_of_split_error (Prover.split sq propagate))
let left () =
  run_updated (fun sq ->
      or_fail
        (function Not_disjunction -> "Goal is not a disjunction")
        (Prover.left sq))
let right () =
  run_updated (fun sq ->
      or_fail
        (function Not_disjunction -> "Goal is not a disjunction")
        (Prover.right sq))
let exists ew =
  run_updated (fun sq ->
      or_fail string_of_exists_error (Prover.exists_tac sq ew))
let apply ?depth ?hint ?(term_witness = ignore) h args ws =
  run_branched (fun sq ->
      or_fail string_of_apply_error
        (Prover.apply sq ?depth ?hint ~term_witness h args ws))
let backchain ?depth ?(term_witness = ignore) h ws =
  run_branched (fun sq ->
      or_fail string_of_backchain_error
        (Prover.backchain sq ?depth ~term_witness h ws))
let induction ?hint ind_args =
  run_updated (fun sq ->
      or_fail string_of_induction_error
        (Prover.induction sq ?hint ind_args))
let coinduction ?hint () =
  run_updated (fun sq ->
      or_fail string_of_coinduction_error (Prover.coinduction sq ?hint ()))
let assert_hyp ?hint ?depth term =
  run_delayed (fun sq ->
      or_fail string_of_assert_error
        (Prover.assert_hyp sq ?hint ?depth term))
let monotone ?hint h t =
  run_delayed (fun sq ->
      or_fail string_of_monotone_error (Prover.monotone sq ?hint h t))
let cut ?hint h arg =
  run_updated (fun sq ->
      or_fail string_of_cut_error (Prover.cut sq ?hint h arg))
let cut_from ?hint h arg term =
  run_updated (fun sq ->
      or_fail string_of_cut_from_error
        (Prover.cut_from sq ?hint h arg term))
let search_cut ?hint h =
  run_updated (fun sq ->
      or_fail string_of_search_cut_error (Prover.search_cut sq ?hint h))
let inst ?hint h ws =
  run_updated (fun sq ->
      or_fail string_of_inst_error (Prover.inst sq ?hint h ws))
let clear cm hs =
  run_updated (fun sq ->
      or_fail string_of_clear_error (Prover.clear sq cm hs))
let clear_duplicates () =
  install_updated (Prover.clear_duplicates (focused ()))
let abbrev ids str =
  install_updated (Prover.abbrev (focused ()) ids str)
let unabbrev ids =
  install_updated (Prover.unabbrev (focused ()) ids)
let rename xfr xto =
  run_updated (fun sq ->
      or_fail string_of_rename_error (Prover.rename sq xfr xto))
let unfold clause_sel sol_sel =
  run_branched (fun sq ->
      or_fail string_of_unfold_error
        (Prover.unfold sq clause_sel sol_sel))
let permute_nominals ids form =
  run_updated (fun sq ->
      or_fail string_of_permute_error (Prover.permute sq ids form))
let saturate ?hint ?depth lemmas =
  run_branched (fun sq ->
      or_fail string_of_saturate_error
        (Prover.saturate sq ?hint ?depth lemmas))

let string_of_compute_error = function
  | Compute.Compute_stmt e -> string_of_stmt_error e
  | Compute.Compute_rename e -> string_of_rename_hint_error e
  | Compute.Compute_out_of_gas n ->
      Printf.sprintf "Compute ran out of gas (given %d) -- looping?" n
  | Compute.Compute_tactic_failure s -> s

let compute ?hint ?gas hs =
  run_branched (fun sq ->
      or_fail string_of_compute_error
        (Compute.compute sq ?hint ?gas hs))

(* Mirror [Driver.eval_tac] on [Try]: recover to a no-op on [Error]. *)
let try_compute ?hint ?gas hs =
  let sq = focused () in
  let snap = State.snapshot () in
  begin match Compute.compute sq ?hint ?gas hs with
  | Ok subs -> install_branched sq subs
  | Error _ -> State.reload snap
  end

(* Mirror [Driver.repeat_tac]: iterate until the first [Error]. *)
let repeat_compute ?(limit = 5) hs =
  let rec loop n =
    if n <= 0 then Alcotest.fail "repeat_compute exceeded limit"
    else
      let snap = State.snapshot () in
      begin match Compute.compute (focused ()) hs with
      | Error _ -> State.reload snap
      | Ok subs ->
          install_branched (focused ()) subs ;
          loop (n - 1)
      end
  in
  loop limit
let skip () =
  let s = !st in
  match s.focused with
  | None -> ignore (focused ())
  | Some sq ->
      st := { s with skip_seen = true } ;
      install_branched sq (Prover.skip sq)
let bullet b =
  st :=
    normalize_focused_state
      (or_fail string_of_bullet_error (Prover.bullet !st b))
let start_proof () = st := { !st with skip_seen = false ; bullets = [] }

let initial_bind_state = Term.get_bind_state ()
let initial_clauses = !clauses
let initial_defs_table = Hashtbl.copy defs_table

let setup_prover ?clauses:(clauses=[])
    ?goal:(goal="") ?lemmas:(lemmas=[]) () =
  State.Undo.set_enabled true ;
  State.Undo.reset () ;
  Term.set_bind_state initial_bind_state ;
  Prover.clauses := initial_clauses ;
  Extensions.Hashtbl.assign defs_table initial_defs_table ;
  Hashtbl.reset Prover.lemmas ;
  Hashtbl.reset Prover.lemma_tags ;
  Prover.add_clauses clauses ;
  let goal =
    if goal = "" then parse_metaterm "true" else freshen goal
  in
  st := Prover.start_proof
      (theorem (empty_sequent placeholder_goal) goal) ;
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
             (List.mem_assoc "R" (focused ()).vars)
        ) ;

      test_case "Intros should raise over support"
        (fun () ->
           setup_prover ()
             ~goal:"forall L, rel1 n1 L" ;

           intros no_hints ;
           assert_goal "rel1 n1 (L n1)"
        ) ;

      test_case "Intros on multiple nabla variables"
        (fun () ->
           setup_prover ()
             ~goal:"nabla (x:i) y, x = y" ;

           intros no_hints ;
           assert_goal "n1 = n2"
        ) ;

      test_case "Assert test"
        (fun () ->
           setup_prover ()
             ~goal:"{a}" ;

           assert_hyp (parse_umetaterm "{b}") ;
           assert_n_subgoals 2 ;

           assert_pprint_equal "{b}" (focused ()).goal ;
           skip () ;
           assert_n_subgoals 1 ;

           assert_pprint_equal "{a}" (focused ()).goal ;
           match (focused ()).hyps with
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
             (focused ()).goal ;

           skip () ;
           assert_n_subgoals 1 ;
           match (focused ()).hyps with
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

           assert_pprint_equal "{A}" (focused ()).goal ;

           skip () ;
           match (focused ()).hyps with
             | [] -> assert_pprint_equal "{B}" (focused ()).goal
             | _ -> Alcotest.fail "Expected no hypotheses"
        ) ;

      test_case "SplitStar test"
        (fun () ->
           setup_prover ()
             ~goal:"{A} /\\ {B}" ;

           split true ;
           assert_n_subgoals 2 ;

           assert_pprint_equal "{A}" (focused ()).goal ;

           skip () ;
           match (focused ()).hyps with
             | [h] ->
                 assert_pprint_equal "{A}" h.term ;
                 assert_pprint_equal "{B}" (focused ()).goal
             | _ -> Alcotest.fail "Expected one hypothesis"
        ) ;

      test_case "Split many test"
        (fun () ->
           setup_prover ()
             ~goal:"({A} /\\ {B}) /\\ ({C} /\\ {D})" ;

           split false ;
           assert_n_subgoals 4 ;

           assert_pprint_equal "{A}" (focused ()).goal ;
           skip () ;
           assert_pprint_equal "{B}" (focused ()).goal ;
           skip () ;
           assert_pprint_equal "{C}" (focused ()).goal ;
           skip () ;
           assert_pprint_equal "{D}" (focused ()).goal
        ) ;

      test_case "SplitStar many test"
        (fun () ->
           setup_prover ()
             ~goal:"{A} /\\ {B} /\\ {C}" ;

           split true ;
           assert_n_subgoals 3 ;

           assert_pprint_equal "{A}" (focused ()).goal ;

           skip () ;
           begin match (focused ()).hyps with
             | [h] ->
                 assert_pprint_equal "{A}" h.term ;
                 assert_pprint_equal "{B}" (focused ()).goal
             | _ -> Alcotest.fail "Expected one hypothesis"
           end ;

           skip () ;
           begin match (focused ()).hyps with
             | [h1; h2] ->
                 assert_pprint_equal "{A}" h1.term ;
                 assert_pprint_equal "{B}" h2.term ;
                 assert_pprint_equal "{C}" (focused ()).goal
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

           assert_pprint_equal "foo t1" (focused ()).goal) ;

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
           assert_pprint_equal "bar B" (focused ()).goal ;

           skip () ;
           assert_n_subgoals 1 ;
           assert_pprint_equal "baz B" (focused ()).goal ;
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

           intros no_hints ;
           case (keep "H1") ;
           assert_n_subgoals 2 ;
           Alcotest.check (Alcotest.list Alcotest.string) "string lists differ" ["H1"; "H2"]
             (List.map (fun h -> h.id) (focused ()).hyps) ;

           search () ;
           assert_n_subgoals 1 ;

           Alcotest.check (Alcotest.list Alcotest.string) "hypotheses"
             ["H1"; "H2"; "H3"] (List.map (fun h -> h.id) (focused ()).hyps)
        ) ;

      test_case "Skip should remove current subcase"
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V, {typeof P V} -> {typeof P V}" ;

           intros no_hints ;
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
                  intros no_hints ;
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

      test_case "Get lemma should reject instantiation with prop"
        (fun () ->
           setup_prover () ;
           Term.schematic_instantiations := [] ;
           ignore (add_lemma "bad" ["A"]
                     (parse_metaterm "forall (x:A), poly x")) ;
           Alcotest.check_raises
             "Explicit instantiation with prop"
             (Failure "Type argument bad may not contain prop")
             (fun () ->
                ignore (or_fail string_of_stmt_error
                          (get_lemma ~tys:[Term.propty] "bad"))) ;
           Alcotest.check_raises
             "Explicit instantiation with type containing prop"
             (Failure "Type argument bad may not contain prop")
             (fun () ->
                ignore (or_fail string_of_stmt_error
                          (get_lemma
                             ~tys:[Term.tyarrow [Term.propty] Term.propty]
                             "bad"))) ;
           Term.schematic_instantiations := [] ;
           ignore (or_fail string_of_stmt_error
                     (get_lemma ~tys:[ity] "bad")) ;
           Checks.ensure_no_prop_schematic_instantiation () ;
           Term.schematic_instantiations := []
        ) ;

      test_case "Undo should restore previous save state"
        (fun () ->
           setup_prover ()
             ~clauses:eval_clauses
             ~goal:"forall P V T, {eval P V} -> {typeof P T} -> {typeof V T}" ;

           induction [1] ;
           intros no_hints ;
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
                  intros no_hints ;

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
                  intros no_hints ;
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
                  intros no_hints ;

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

           add_defs_for ["bar"] Types.CoInductive
             (parse_defs "bar X := bar X.") ;

           coinduction () ;
           assert_search_fails ()
        );

      test_case "Search should find simple co-inductive hypothesis"
        (fun () ->
           setup_prover ()
             ~goal:"bar X" ;

           add_defs_for ["bar"] Types.CoInductive
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

           add_defs_for ["foo"] Types.Inductive
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

           add_defs_for ["bar"] Types.CoInductive
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

           intros no_hints ;
           Alcotest.match_raises "expected exception" (fun _ -> true)
             (fun () -> ignore (apply (keep "lem") (List.map keep ["H1"]) [])) ;
        );

      test_case "Case-analysis with nabla in the head, two in a row"
        (fun () ->
           setup_prover ()
             ~goal:"forall X Y, foo X -> foo Y -> \
                          (X = Y \\/ (X = Y -> false))" ;

           add_defs_for ["foo"] Types.Inductive
             (parse_defs "nabla x, foo x.") ;

           assert_proof
             (fun () ->
                intros no_hints ;
                case (remove "H1") ;
                assert_n_subgoals 1 ;

                case (remove "H2") ;
                assert_n_subgoals 2 ;

                right () ;
                intros no_hints ;
                case (remove "H3") ;
                assert_n_subgoals 1 ;

                search ()
             )
        ) ;

      test_case "Induction within coinduction should fail"
        (fun () ->
           setup_prover ()
             ~goal:"forall X, foo X -> bar X" ;

           add_defs_for ["foo"] Types.Inductive
             (parse_defs "foo X := foo X.") ;
           add_defs_for ["bar"] Types.CoInductive
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

           add_defs_for ["foo"] Types.Inductive
             (parse_defs "foo X := foo X.") ;
           add_defs_for ["bar"] Types.CoInductive
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
                intros no_hints ;
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

             intros no_hints ;
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
             ["H1"; "H2"] (List.map (fun h -> h.id) (focused ()).hyps) ;
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
             ["H1"; "H2"; "H3"] (List.map (fun h -> h.id) (focused ()).hyps) ;
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
             ["H1"; "H2"] (List.map (fun h -> h.id) (focused ()).hyps) ;
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
             ["H1"; "H2"; "H3"] (List.map (fun h -> h.id) (focused ()).hyps) ;
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
             [] (List.map (fun h -> h.id) (focused ()).hyps)
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
             ["H1"; "H3"; "H4"] (List.map (fun h -> h.id) (focused ()).hyps)
        ) ;

      test_case "Skip should mark the proof as unfinished"
        (fun () ->
           setup_prover () ~goal:"true /\\ true" ;

           split false ;
           start_proof () ;
           skip () ;
           search () ;
           Alcotest.check Alcotest.bool
             "proof should be unfinished" true
             (is_completed !st && (!st).skip_seen)
        ) ;

      test_case "Start proof should reset the skipped status"
        (fun () ->
           setup_prover () ~goal:"true" ;

           start_proof () ;
           search () ;
           Alcotest.check Alcotest.bool
             "proof should be finished" true
             (is_completed !st && not (!st).skip_seen)
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

           add_defs_for ["foo"] Types.Inductive
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
                (fun h -> h.abbrev = Some "both") (focused ()).hyps) ;

           unabbrev (Term.Iset.of_list ["H1"]) ;
           match (focused ()).hyps with
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

           monotone ?hint:(hyp_hint "M") (keep "H1")
             (parse_uterm "a :: b :: nil") ;

           assert_n_subgoals 2 ;
           skip () ;
           assert_n_subgoals 1 ;
           match (focused ()).hyps with
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
             [] (List.map (fun h -> h.id) (focused ()).hyps) ;
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
                intros no_hints ;
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
           add_defs_for ["foo155"] Types.Inductive
             (parse_defs "foo155 (mu155 k\\ E k) \
                          (mu155 k_\\ E (o\\ o)).") ;
           intros no_hints ;
           case (keep "H1") ;
           assert_n_subgoals 1 ;
           assert_pprint_equal
             "foo155 (mu155 (x1\\E1 n1 x1)) (mu155 (x1\\E1 n1 x2\\x2))"
             (get_hyp "H1")
        ) ;

      test_case "Case hspec names variables and hypotheses per subgoal"
        (fun () ->
           setup_prover ()
             ~goal:"forall (X:i), \
                    (exists (Y:i), rel1 X Y) \\/ \
                    (exists (Z:i), rel1 X Z) -> false" ;
           intros no_hints ;
           let hint =
             Some [ user_alt ["U"] ["H1"] ;
                    user_alt ["V"] ["H2"] ]
           in
           case ?hint (remove "H1") ;
           assert_n_subgoals 2 ;
           Alcotest.check Alcotest.bool "first variable" true
             (List.mem_assoc "U" (focused ()).vars) ;
           Alcotest.check Alcotest.bool "first hypothesis" true
             (List.exists (fun h -> h.id = "H1") (focused ()).hyps) ;
           skip () ;
           Alcotest.check Alcotest.bool "second variable" true
             (List.mem_assoc "V" (focused ()).vars) ;
           Alcotest.check Alcotest.bool "second hypothesis" true
             (List.exists (fun h -> h.id = "H2") (focused ()).hyps)
        ) ;

      test_case "A single hspec alternative applies to every subgoal"
        (fun () ->
           setup_prover ()
             ~goal:"forall (X:i), \
                    (exists (Y:i), rel1 X Y) \\/ \
                    (exists (Z:i), rel1 X Z) -> false" ;
           intros no_hints ;
           let hint = Some [ user_alt ["U"] ["H"] ] in
           case ?hint (remove "H1") ;
           assert_n_subgoals 2 ;
           Alcotest.check Alcotest.bool "first variable" true
             (List.mem_assoc "U" (focused ()).vars) ;
           Alcotest.check Alcotest.bool "first hypothesis" true
             (List.exists (fun h -> h.id = "H") (focused ()).hyps) ;
           skip () ;
           Alcotest.check Alcotest.bool "second variable" true
             (List.mem_assoc "U" (focused ()).vars) ;
           Alcotest.check Alcotest.bool "second hypothesis" true
             (List.exists (fun h -> h.id = "H") (focused ()).hyps)
        ) ;

      test_case "Intros hspec names variables and hypotheses"
        (fun () ->
           setup_prover ()
             ~goal:"forall (X:i) (Y:i), rel1 X Y -> rel1 X Y" ;
           intros (user_alt ["U"; "V"] ["H"]) ;
           Alcotest.check Alcotest.bool "first variable" true
             (List.mem_assoc "U" (focused ()).vars) ;
           Alcotest.check Alcotest.bool "second variable" true
             (List.mem_assoc "V" (focused ()).vars) ;
           Alcotest.check Alcotest.bool "hypothesis" true
             (List.exists (fun h -> h.id = "H") (focused ()).hyps)
        ) ;

      test_case "Intros hspec repeats the last hint and honors don't-care"
        (fun () ->
           setup_prover ()
             ~goal:"forall (X:i) (Y:i), \
                    rel1 X Y -> rel1 X Y -> rel1 X Y" ;
           intros { hspec_vars = [User_name "U"; Dont_care] ;
                    hspec_hyps = [User_name "H"] } ;
           Alcotest.check Alcotest.bool "first variable" true
             (List.mem_assoc "U" (focused ()).vars) ;
           Alcotest.check Alcotest.bool "second variable was not hinted"
             false (List.mem_assoc "U1" (focused ()).vars) ;
           Alcotest.check Alcotest.bool "first hypothesis" true
             (List.exists (fun h -> h.id = "H") (focused ()).hyps) ;
           Alcotest.check Alcotest.bool "repeated hypothesis" true
             (List.exists (fun h -> h.id = "H1") (focused ()).hyps)
        ) ;

      test_case "Intros names a nabla variable with a nominal hint"
        (fun () ->
           setup_prover ~goal:"nabla (x:i), x = x" () ;
           intros { hspec_vars = [User_name "n34"] ; hspec_hyps = [] } ;
           assert_pprint_equal "n34 = n34" (focused ()).goal
        ) ;

      test_case "A nominal hint already free in the body is an error"
        (fun () ->
           setup_prover ~goal:"nabla (x:i), x = n34" () ;
           Alcotest.check_raises
             "free nominal hint"
             (Failure "Nominal hint \"n34\" is already free in the subgoal")
             (fun () ->
                intros { hspec_vars = [User_name "n34"] ;
                         hspec_hyps = [] })
        ) ;

      test_case "An eigenvariable hint cannot be a nominal name"
        (fun () ->
           setup_prover ~goal:"forall (X:i), X = X" () ;
           Alcotest.check_raises
             "reserved nominal hint"
             (Failure "Hint \"n34\" is reserved for nominal constants")
             (fun () ->
                intros { hspec_vars = [User_name "n34"] ; hspec_hyps = [] })
        ) ;

      test_case "A nabla hint must be a nominal name"
        (fun () ->
           setup_prover ~goal:"nabla (x:i), x = x" () ;
           Alcotest.check_raises
             "non-nominal nabla hint"
             (Failure
                "Hint \"u\" is not a valid nominal constant name; \
                 use n<number>")
             (fun () ->
                intros { hspec_vars = [User_name "u"] ; hspec_hyps = [] })
        ) ;

      test_case "Nested bullets and unfocused display"
        (fun () ->
           setup_prover
             ~goal:"(true -> true /\\ true) /\\ \
                    (true -> true /\\ (true -> true /\\ true))" () ;
           start_proof () ;
           assert_proof begin fun () ->
             split false ;
             bullet "-" ;
               intros no_hints ;
               split false ;
               bullet "+" ; search () ;
               Alcotest.check Alcotest.bool "unfocused at +" false
                 (is_focused ()) ;
               Alcotest.check (Alcotest.option Alcotest.string) "expect +"
                 (Some "+") (expected_bullet ()) ;
               Alcotest.check Alcotest.string "unfocused display"
                 "\nSubgoal completed. Focus next subgoal with bullet + \
                  (2 subgoals remaining).\n\n"
                 (get_display ()) ;
               bullet "+" ; search () ;
             Alcotest.check Alcotest.bool "unfocused at -" false
               (is_focused ()) ;
             Alcotest.check (Alcotest.option Alcotest.string) "expect -"
               (Some "-") (expected_bullet ()) ;
             bullet "-" ;
               intros no_hints ;
               split false ;
               bullet "+" ; search () ;
               bullet "+" ;
                 intros no_hints ;
                 split false ;
                 bullet "*" ; search () ;
                 bullet "*" ; search ()
           end
        ) ;

      test_case "Tactic fails while unfocused"
        (fun () ->
           setup_prover ~goal:"true /\\ true" () ;
           start_proof () ;
           split false ;
           bullet "-" ;
           search () ;
           Alcotest.check Alcotest.bool "unfocused" false (is_focused ()) ;
           Alcotest.check_raises "tactic unfocused"
             (Failure
                "No focused subgoal. Use bullet - to focus the next subgoal")
             (fun () -> search ())
        ) ;

      test_case "Wrong bullet fails while unfocused"
        (fun () ->
           setup_prover ~goal:"true /\\ true" () ;
           start_proof () ;
           split false ;
           bullet "-" ;
           search () ;
           Alcotest.check_raises "wrong bullet"
             (Failure "Wrong bullet +: expected -")
             (fun () -> bullet "+")
        ) ;

      test_case "Reusing enclosing bullet fails while focused"
        (fun () ->
           setup_prover ~goal:"(true -> true /\\ true) /\\ true" () ;
           start_proof () ;
           split false ;
           bullet "-" ;
           intros no_hints ;
           split false ;
           Alcotest.check_raises "reused enclosing bullet"
             (Failure "Bullet - is already active in an enclosing subgoal")
             (fun () -> bullet "-")
        ) ;

      test_case "Strict sibling bullets and inner bullet auto-close"
        (fun () ->
           setup_prover
             ~goal:"(true -> true /\\ true) /\\ \
                    (true -> true /\\ true) /\\ true" () ;
           start_proof () ;
           assert_proof begin fun () ->
             split false ;
             bullet "-" ;
               intros no_hints ;
               split false ;
               bullet "+" ; search () ;
               bullet "+" ; search () ;
             Alcotest.check Alcotest.bool "second - unfocused" false
               (is_focused ()) ;
             bullet "-" ;
               intros no_hints ;
               split false ;
               bullet "+" ; search () ;
               bullet "+" ; search () ;
             Alcotest.check Alcotest.bool "third - unfocused" false
               (is_focused ()) ;
             Alcotest.check (Alcotest.option Alcotest.string) "expect -"
               (Some "-") (expected_bullet ()) ;
             bullet "-" ;
               search ()
           end
        ) ;

      test_case "Undo restores bullet stack and focus"
        (fun () ->
           setup_prover ~goal:"true /\\ true" () ;
           start_proof () ;
           split false ;
           bullet "-" ;
           search () ;
           Alcotest.check Alcotest.bool "unfocused before bullet" false
             (is_focused ()) ;
           State.Undo.push () ;
           bullet "-" ;
           Alcotest.check Alcotest.bool "focused after bullet" true
             (is_focused ()) ;
           State.Undo.undo () ;
           Alcotest.check Alcotest.bool "unfocused after undo" false
             (is_focused ()) ;
           Alcotest.check (Alcotest.option Alcotest.string)
             "expected bullet after undo" (Some "-") (expected_bullet ())
        ) ;

      test_case "Nested bullet pushes rather than replaces outer frame"
        (fun () ->
           setup_prover ~goal:"(true -> true /\\ true) /\\ true" () ;
           start_proof () ;
           split false ;
           bullet "-" ;
           intros no_hints ;
           split false ;
           bullet "+" ;
           Alcotest.check Alcotest.int "bullet depth" 2
             (List.length (!st).bullets) ;
           Alcotest.check Alcotest.int "outer siblings kept" 1
             (match (!st).bullets with
              | _ :: outer :: _ -> List.length outer.siblings
              | _ -> Alcotest.fail "expected nested bullet frames") ;
           search () ;
           Alcotest.check Alcotest.bool "unfocused at +" false
             (is_focused ()) ;
           bullet "+" ;
           search () ;
           Alcotest.check Alcotest.bool "unfocused at -" false
             (is_focused ()) ;
           Alcotest.check (Alcotest.option Alcotest.string) "expect -"
             (Some "-") (expected_bullet ()) ;
           bullet "-" ;
           search () ;
           Alcotest.check Alcotest.bool "proof completed" true
             (is_completed !st)
        ) ;

      test_case "Try compute recovers from failure"
        (fun () ->
           setup_prover ~goal:"{a}" () ;
           add_hyp (freshen "{b}") ;
           let goal_before = metaterm_to_string (focused ()).goal in
           begin match Compute.compute (focused ()) [remove "H9"] with
           | Ok _ -> Alcotest.fail "compute with unknown hyp should fail"
           | Error (Compute.Compute_stmt _) -> ()
           | Error e ->
               Alcotest.fail ("unexpected compute error: " ^
                                string_of_compute_error e)
           end ;
           try_compute [remove "H9"] ;
           assert_n_subgoals 1 ;
           Alcotest.check Alcotest.string "goal unchanged" goal_before
             (metaterm_to_string (focused ()).goal) ;
           compute [] ;
           assert_n_subgoals 1 ;
           Alcotest.check Alcotest.string "error string"
             "Could not find hypothesis or lemma H9"
             (string_of_compute_error
                (Compute.Compute_stmt (Unknown_stmt "H9")))
        ) ;

      test_case "Repeat compute stops on failure"
        (fun () ->
           setup_prover ~goal:"{a}" () ;
           add_hyp (freshen "{b}") ;
           let goal_before = metaterm_to_string (focused ()).goal in
           repeat_compute [remove "H9"] ;
           assert_n_subgoals 1 ;
           Alcotest.check Alcotest.string "goal unchanged" goal_before
             (metaterm_to_string (focused ()).goal)
        ) ;


    ]
