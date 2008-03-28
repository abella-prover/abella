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
open Extensions
open Printf

let quiet = ref false
let interactive = ref false

let annotate = ref false
let count = ref 0

exception AbortProof

let ensure_no_restrictions term =
  if get_max_restriction term > 0 then
    failwith "Cannot use restrictions: *, @ or +"
      
let warn_if_free_vars free_vars =
  if free_vars <> [] then begin
    printf "\n\tWarning: Potential variables treated as constants: %s\n\n"
      (String.concat ", " free_vars) ;
    if not !interactive then exit 1
  end

let warn_def_usage ?(ignore=[]) term =
  let rec aux term =
    match term with
      | True | False | Eq _ | Obj _ -> ()
      | Arrow(a, b) -> aux a; aux b
      | Binding(_, _, body) -> aux body
      | Or(a, b) -> aux a; aux b
      | And(a, b) -> aux a; aux b
      | Pred(pred, _) ->
          let psig = Term.term_sig pred in
            if not (Hashtbl.mem defs psig) && not (List.mem psig ignore) then
              begin
                printf "\n\tWarning: %s is not defined." (sig_to_string psig) ;
                printf "\n\tPerhaps it is mispelt or you meant {%s}.\n\n"
                  (Term.term_to_string pred) ;
                if not !interactive then exit 1
              end
  in
    aux term

let check_theorem thm =
  ensure_no_restrictions thm ;
  warn_def_usage thm ;
  let free_vars = Tactics.free_capital_var_names thm in
    warn_if_free_vars free_vars

let check_def (head, body) =
  ensure_no_restrictions head ;
  ensure_no_restrictions body ;
  let head_vars = Tactics.free_capital_var_names head in
  let body_vars = Tactics.free_capital_var_names body in
  let free_vars = List.minus body_vars head_vars in
    warn_if_free_vars free_vars ;
    warn_def_usage ~ignore:[def_sig (head, body)] body


let rec process_proof name lexbuf =
  let finished = ref false in
    try while not !finished do try
      if not !quiet then begin
        if !annotate then begin
          printf "</pre>\n" ;
          incr count ;
          printf "<a name=\"%d\"></a>\n" !count ;
          printf "<pre>\n"
        end ;
        display () ;
        printf "%s < %!" name
      end ;
      let input = Parser.command Lexer.token lexbuf in
        if not !interactive && not !quiet then begin
          let pre, post = if !annotate then "<b>", "</b>" else "", "" in
            printf "%s%s.%s\n" pre (command_to_string input) post
        end ;
        begin match input with
          | Induction(arg) -> induction arg
          | CoInduction -> coinduction ()
          | Apply(h, args, ws) -> apply h args ws
          | Cut(h, arg) -> cut h arg
          | Inst(h, n, t) -> inst h n t
          | Case(str, keep) -> case ~keep str
          | Assert(t) ->
              ensure_no_restrictions t ;
              warn_def_usage t ;
              assert_hyp t
          | Exists(t) -> exists t
          | Clear(hs) -> clear hs
          | Search -> search ~interactive:!interactive ()
          | Split -> split false
          | SplitStar -> split true
          | Unfold -> unfold ()
          | Intros -> intros ()
          | Skip -> skip ()
          | Abort -> raise AbortProof
          | Undo -> undo ()
        end ;
        if !interactive then flush stdout ;
    with
      | Failure "lexing: empty token" ->
          exit (if !interactive then 0 else 1)
      | Failure "Proof completed." ->
          print_endline "Proof completed." ;
          reset_prover () ;
          finished := true
      | Failure s ->
          printf "Error: %s\n" s ;
          if not !interactive then exit 1
      | End_of_file ->
          print_endline "Proof NOT completed." ;
          exit 1
      | AbortProof ->
          print_endline "Proof aborted." ;
          reset_prover () ;
          raise AbortProof
      | e ->
          printf "Error: %s\n%!" (Printexc.to_string e) ;
          if not !interactive then exit 1
    done with
      | Failure "eof" -> ()

let rec process lexbuf =
  try while true do try
    if !annotate then begin
      incr count ;
      printf "<a name=\"%d\"></a>\n" !count ;
      printf "<pre class=\"code\">\n"      
    end ;
    printf "Abella < %!" ;
    let input = Parser.top_command Lexer.token lexbuf in
      if not !interactive then begin
          let pre, post = if !annotate then "<b>", "</b>" else "", "" in
            printf "%s%s.%s\n" pre (top_command_to_string input) post
      end ;
      begin match input with
        | Theorem(name, thm) ->
            check_theorem thm ;
            theorem thm ;
            begin try
              process_proof name lexbuf ;
              add_lemma name thm
            with AbortProof -> () end
        | Axiom(name, axiom) ->
            check_theorem axiom ;
            add_lemma name axiom
        | Define(def) ->
            check_def def ;
            add_def Inductive def
        | CoDefine(def) ->
            check_def def ;
            add_def CoInductive def
      end ;
      if !interactive then flush stdout ;
      if !annotate then printf "</pre>" ;
      print_newline ()
  with
    | Failure "lexing: empty token" ->
        exit (if !interactive then 0 else 1)
    | Failure s ->
        printf "Error: %s\n" s ;
        if not !interactive then exit 1
    | End_of_file ->
        print_endline "Goodbye." ;
        if !annotate then printf "</pre>\n" ;
        exit 0
    | e ->
        printf "Unknown error: %s\n%!" (Printexc.to_string e) ;
        if not !interactive then exit 1
  done with
  | Failure "eof" -> ()

let welcome_msg = sprintf "Welcome to Abella %s\n" Version.version

let usage_message = "abella [options] <module-file>"

let command_input = ref ""

let options =
  Arg.align
    [
      ("-f", Arg.Set_string command_input,
       "<theorem-file> Read command input from file") ;
      ("-q", Arg.Set quiet, " Quiet mode") ;
      ("-a", Arg.Set annotate, " Annotate mode") ;
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
  match !command_input with
    | "" ->
        interactive := true ;
        process (Lexing.from_channel stdin)
    | name ->
        interactive := false ;
        process (Lexing.from_channel (open_in name))
        
