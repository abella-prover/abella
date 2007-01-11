open OUnit
open Prover
open Lppterm
open Term

let eval_clauses =
  Parser.clauses Lexer.token (Lexing.from_channel (open_in "eval.mod"))
    
let pcf_clauses =
  Parser.clauses Lexer.token (Lexing.from_channel (open_in "pcf.mod"))

let parse str =
  Top_parser.lppterm Top_lexer.token (Lexing.from_string str)

let parse_term str =
  Parser.term Lexer.token (Lexing.from_string str)

let assert_int_equal = assert_equal ~printer:string_of_int

let assert_length_equal n lst =
  assert_int_equal n (List.length lst)

let assert_string_list_equal lst1 lst2 =
  assert_int_equal (List.length lst1) (List.length lst2) ;
  ignore (List.map2 (assert_equal ~printer:(fun s -> s)) lst1 lst2)
    
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
           assert_length_equal 1 !subgoals ;
           
           search () ;
           assert_length_equal 0 !subgoals ;

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
           assert_length_equal 1 !subgoals ;
           assert_string_list_equal ["H1"; "H2"] (List.map fst !hyps) ;
           
           search () ;
           assert_length_equal 0 !subgoals ;

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
           assert_length_equal 12 !subgoals ;
           
           search () ;
           assert_length_equal 11 !subgoals ;

           search () ;
           assert_length_equal 10 !subgoals ;

           search () ;
           assert_length_equal 9 !subgoals ;

           case "H2" ;
           apply "IH" ["H3"; "H4"] ;
           search () ;
           assert_length_equal 8 !subgoals ;

           case "H2" ;
           search () ;
           assert_length_equal 7 !subgoals ;

           case "H2" ;
           apply "IH" ["H3"; "H4"] ;
           case "H5" ;
           search () ;
           assert_length_equal 6 !subgoals ;

           case "H2" ;
           search () ;
           assert_length_equal 5 !subgoals ;

           case "H2" ;
           search () ;
           assert_length_equal 4 !subgoals ;

           case "H2" ;
           apply "IH" ["H4"; "H6"] ;
           search () ;
           assert_length_equal 3 !subgoals ;

           case "H2" ;
           apply "IH" ["H4"; "H7"] ;
           search () ;
           assert_length_equal 2 !subgoals ;

           search () ;
           assert_length_equal 1 !subgoals ;

           case "H2" ;
           apply "IH" ["H3"; "H5"] ;
           case "H7" ;
           inst "H8" (parse_term "N") ;
           apply "H9" ["H6"] ;
           apply "IH" ["H4"; "H10"] ;
           search () ;
           assert_length_equal 0 !subgoals ;

           case "H2" ;
           inst "H4" (parse_term "rec T R") ;
           apply "H5" ["H2"] ;
           apply "IH" ["H3"; "H6"] ;
           assert_raises (Failure("Proof completed."))
             search ;
        ) ;
    ]
