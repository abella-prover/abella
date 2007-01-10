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
  Parser.lppterm Lexer.token (Lexing.from_string str)

 let tests =
  "Prover" >:::
    [
      "New variables added to context" >::
        (fun () ->
           match Tactics.freshen_capital_vars
             Eigen [parse "{eval A B}"] [] with
               | [hyp] ->
                   vars := ["A"; "B"] ;
                   hyps := [("H1", hyp)] ;
                   goal := obj (const "placeholder") ;
                   subgoals := [] ;
                   case "H1" !vars ;
                   assert_bool "R should be added to variable list"
                     (List.mem "R" !vars) ;
               | _ -> assert false
        ) ;
      
    ]
