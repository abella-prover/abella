(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
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
let last_sig = ref ("", 0)

exception AbortProof

let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  let char = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    if file = "" then
      "" (* lexbuf information is rarely accurate at the toplevel *)
    else
      Format.sprintf ": file %s, line %d, character %d" file line char

let ensure_no_restrictions term =
  if get_max_restriction term > 0 then
    failwith "Cannot use restrictions: *, @ or +"

let ensure_no_free_vars free_vars =
  if free_vars <> [] then
    failwith (sprintf "Unbound variables: %s"
                (String.concat ", " free_vars))

let ensure_defs_exist ?(ignore=[]) term =
  term |> iter_preds
      (fun pred ->
         let psig = Term.term_sig pred in
           if not (Hashtbl.mem defs psig) && not (List.mem psig ignore) then
             failwith (sprintf "%s is not defined.\
                                \ Perhaps it is mispelt or you meant {%s}."
                         (sig_to_string psig) (Term.term_to_string pred)))

let warn_stratify dsig term =
  let rec aux term =
    match term with
      | Arrow(left, right) ->
          (List.exists (fun s -> s = dsig) (map_preds Term.term_sig left))
          || aux right
      | Binding(_, _, body) -> aux body
      | Or(left, right) -> aux left || aux right
      | And(left, right) -> aux left || aux right
      | _ -> false
  in
    if aux term then begin
      printf "Warning: %s might not be stratified" (sig_to_string dsig)
    end

let check_theorem thm =
  ensure_no_restrictions thm ;
  ensure_defs_exist thm ;
  ensure_no_free_vars (Tactics.free_capital_var_names thm)

let ensure_new_or_last_sig dsig =
  if Hashtbl.mem defs dsig then
    if dsig <> !last_sig then
      failwith (sprintf "%s has already been defined" (sig_to_string dsig)) ;
  last_sig := dsig

let ensure_not_capital (name, _) =
  if Tactics.is_capital name then
    failwith (sprintf "Defined predicates may not begin with \
                       a capital letter.")

let check_def (head, body) =
  ensure_no_restrictions head ;
  ensure_no_restrictions body ;
  let head_vars = Tactics.free_capital_var_names head in
  let body_vars = Tactics.free_capital_var_names body in
  let free_vars = List.minus body_vars head_vars in
  let dsig = def_sig (head, body) in
    ensure_not_capital dsig ;
    ensure_new_or_last_sig dsig ;
    ensure_no_free_vars free_vars ;
    ensure_defs_exist ~ignore:[dsig] body ;
    warn_stratify dsig body

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
        save_undo_state () ;
        begin match input with
          | Induction(args) -> induction args
          | CoInduction -> coinduction ()
          | Apply(h, args, ws) -> apply h args ws
          | Cut(h, arg) -> cut h arg
          | Inst(h, n, t) -> inst h n t
          | Case(str, keep) -> case ~keep str
          | Assert(t) ->
              ensure_no_restrictions t ;
              ensure_defs_exist t ;
              ensure_no_free_vars
                (List.minus
                   (Tactics.free_capital_var_names t)
                   (List.map fst sequent.vars)) ;
              assert_hyp t
          | Exists(t) -> exists t
          | Monotone(h, t) -> monotone h t
          | Clear(hs) -> clear hs
          | Search(limit) -> search ~limit ~interactive:!interactive ()
          | Split -> split false
          | SplitStar -> split true
          | Left -> left ()
          | Right -> right ()
          | Unfold -> unfold ()
          | Intros -> intros ()
          | Skip -> skip ()
          | Abort -> raise AbortProof
          | Undo -> undo () ; undo () (* undo recent save, and previous save *)
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
      | Parsing.Parse_error ->
          Format.printf "Syntax error%s.\n%!" (position lexbuf) ;
          Lexing.flush_input lexbuf ;
          if not !interactive then exit 1
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
              add_lemma name thm ;
              last_sig := ("", 0)
            with AbortProof -> () end
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
    | Parsing.Parse_error ->
        Format.printf "Syntax error%s.\n%!" (position lexbuf) ;
        Lexing.flush_input lexbuf ;
        if not !interactive then exit 1
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

let lexbuf_from_file filename =
  let lexbuf = Lexing.from_channel (open_in filename) in
    lexbuf.Lexing.lex_curr_p <- {
      lexbuf.Lexing.lex_curr_p with
        Lexing.pos_fname = filename } ;
    lexbuf

let parse_mod_file name =
  if not !quiet then
    Format.printf "Reading clauses from %s\n%!" name ;
  let lexbuf = lexbuf_from_file name in
    try
      add_clauses (Parser.clauses Lexer.token lexbuf)
    with
      | Parsing.Parse_error ->
          Format.printf "Syntax error%s.\n%!" (position lexbuf) ;
          exit 1

let _ =
  printf "%s%!" welcome_msg ;
  Arg.parse options parse_mod_file usage_message ;
  match !command_input with
    | "" ->
        interactive := true ;
        process (Lexing.from_channel stdin)
    | name ->
        interactive := false ;
        process (lexbuf_from_file !command_input)

