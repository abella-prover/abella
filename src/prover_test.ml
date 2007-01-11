open OUnit
open Prover
open Lppterm
open Term

let clauses_str =
  "eval (abs R) (abs R).\n" ^
    "eval (app M N) V :- eval M (abs R), eval (R N) V.\n" ^
    "typeof (abs R) (arrow T U) :- pi x\\ (typeof x T => typeof (R x) U).\n" ^
    "typeof (app M N) T :- typeof M (arrow U T), typeof N U."

let _ =
  Prover.clauses :=
    Parser.clauses Lexer.token (Lexing.from_string clauses_str)

let parse str =
  Top_parser.lppterm Top_lexer.token (Lexing.from_string str)

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
           match Tactics.freshen_capital_vars
             Eigen [parse "{eval A B}"] [] with
               | [hyp] ->
                   reset_prover () ;
                   vars := ["A"; "B"] ;
                   hyps := [("H1", hyp)] ;
                   case "H1" ;
                   assert_bool "R should be added to variable list"
                     (List.mem "R" !vars) ;
               | _ -> assert false
        ) ;
      
      "Eval example" >::
        (fun () ->
           reset_prover () ;
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
           apply "H8" ["N"] ;
           apply "H9" ["H6"] ;
           apply "IH" ["H4"; "H10"] ;
           assert_raises (Failure("Proof completed."))
             search ;
        ) ;

      "Cases should not consume fresh hyp names" >::
        (fun () ->
           reset_prover () ;
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

    ]
