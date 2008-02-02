(****************************************************************************)
(* Copyright (C) 2007-2008 Gacek                                            *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

open Metaterm
open Prover
open Types
open Printf

let quiet = ref false

exception AbortProof

let check_theorem thm =
  let variables = Tactics.free_capital_var_names thm in
    if variables <> [] then
      printf "\n\tWarning! Potential variables treated as constants: %s\n\n"
        (String.concat ", " variables)

let rec process_proof name ~interactive lexbuf =
  let finished = ref false in
    try while not !finished do try
      if not !quiet then begin
        display () ;
        printf "%s < %!" name
      end ;
      let input = Parser.command Lexer.token lexbuf in
        if not interactive && not !quiet then
          printf "%s.\n\n" (command_to_string input) ;
        begin match input with
          | Induction(arg) -> induction arg
          | Apply(h, args) -> apply h args
          | Cut(h, arg) -> cut h arg
          | Inst(h, n, t) -> inst h n t
          | Case(str, keep) -> case ~keep str
          | Assert(t) -> assert_hyp t
          | Exists(t) -> exists t
          | Clear(hs) -> clear hs
          | Search -> search ~interactive ()
          | Split -> split false
          | SplitStar -> split true
          | Unfold -> unfold ()
          | Intros -> intros ()
          | Skip -> skip ()
          | Abort -> raise AbortProof
          | Undo -> undo ()
        end ;
        if interactive then flush stdout
    with
      | Failure "lexing: empty token" ->
          exit (if interactive then 0 else 1)
      | Failure "Proof completed." ->
          print_endline "Proof completed." ;
          reset_prover () ;
          finished := true
      | Failure s ->
          printf "Error: %s\n" s ;
          if not interactive then exit 1
      | End_of_file ->
          print_endline "Proof NOT completed." ;
          exit 1
      | AbortProof ->
          print_endline "Proof aborted." ;
          reset_prover () ;
          raise AbortProof
      | e ->
          printf "Error: %s\n%!" (Printexc.to_string e) ;
          if not interactive then exit 1
    done with
      | Failure "eof" -> ()

let rec process ~interactive lexbuf =
  try while true do try
    printf "Abella < %!" ;
    let input = Parser.top_command Lexer.token lexbuf in
      if not interactive then printf "%s.\n\n" (top_command_to_string input) ;
      begin match input with
        | Theorem(name, thm) ->
            check_theorem thm ;
            theorem thm ;
            begin try
              process_proof ~interactive name lexbuf ;
              add_lemma name thm
            with AbortProof -> () end
        | Axiom(name, axiom) ->
            add_lemma name axiom
        | Def(meta_clause) ->
            add_meta_clause meta_clause
      end ;
      if interactive then flush stdout
  with
    | Failure "lexing: empty token" ->
        exit (if interactive then 0 else 1)
    | Failure s ->
        printf "Error: %s\n" s ;
        if not interactive then exit 1
    | End_of_file ->
        print_endline "Goodbye." ;
        exit 0
    | e ->
        printf "Unknown error: %s\n%!" (Printexc.to_string e) ;
        if not interactive then exit 1
  done with
  | Failure "eof" -> ()

let welcome_msg = "Welcome to Abella 1.0\n"

let usage_message = "abella [options] <module-file>"

let command_input = ref ""

let options =
  Arg.align
    [
      ("-f", Arg.Set_string command_input,
       "<theorem-file> Read command input from file") ;
      ("-q", Arg.Set quiet, " Quiet mode")
    ]

let _ =
  printf "%s%!" welcome_msg ;
  Arg.parse
    options
    (fun file_name ->
       if not !quiet then
         Printf.printf "Reading clauses from %s\n" file_name ;
       add_clauses (Parser.clauses Lexer.token
                      (Lexing.from_channel (open_in file_name))))
    usage_message ;
  if !command_input = "" then
    process ~interactive:true (Lexing.from_channel stdin)
  else
    process ~interactive:false (Lexing.from_channel (open_in !command_input))
        
