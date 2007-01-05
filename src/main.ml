(****************************************************************************)
(* Bedwyr prover                                                            *)
(* Copyright (C) 2005-2006 David Baelde, Alwen Tiu, Axelle Ziegler          *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

exception Invalid_command
exception Assertion_failed

let welcome_msg =
  "Bedwyr welcomes you.

This software is under GNU Public License.
Copyright (c) 2005-2006 Slimmer project.

For a little help, type #help.
\n"

let usage_msg =
  "Bedwyr prover.
This software is under GNU Public License.
Copyright (c) 2005-2006 Slimmer project.

Usage: bedwyr [filename | option]*
"

let help_msg =
  "Useful commands in query mode:
#help.                               Display this message.
#exit.                               Exit.
#debug [flag].                       Turn debugging on/off (flag=on/off).
#time [flag].                        Turn timing on/off (flag=on/off).
#session \"file_1\" ... \"file_N\".      Load these files as the current \
session.
#reload.                             Reload the current session.
#reset.                              Clears the current session.
#show_table [pred].                  Displays the predicate's table.
Or type in a formula to ask for its verification.
For more information (including commands relevant in definition mode),
see the user guide.

"

let interactive = ref true
let test        = ref false
let session     = ref []
let queries     = ref []

let _ =
  Arg.parse [
      "-I", Arg.Clear interactive,
      "Do not enter interactive mode." ;

      "-t", Arg.Set test, "Run tests in definition files." ;

      "-e", Arg.String (fun s -> queries := s::!queries),
      "Execute query."
    ]
    (fun f -> session := f::!session)
    usage_msg

let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  let char = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    if file = "" then
      "" (* lexbuf information is rarely accurate at the toplevel *)
    else
      Format.sprintf ": file %s, line %d, character %d" file line char

let rec process ?(interactive=false) parse lexbuf =
  try while true do try
    if interactive then Format.printf "?= %!" ;
    begin match parse Lexer.token lexbuf with
      | System.Def (k,h,a,b) -> System.add_clause k h a b
      | System.Query a       -> Prover.toplevel_prove a
      | System.Command (c,a) -> command lexbuf (c,a)
    end ;
    if interactive then flush stdout
  with
    | Failure "eof" as e -> raise e
    | Parsing.Parse_error ->
        Format.printf "Syntax error%s.\n%!" (position lexbuf) ;
        if not interactive then exit 1;
    | Failure "lexing: empty token" ->
        Format.printf "Lexing error%s.\n%!" (position lexbuf) ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | Assertion_failed ->
        Format.printf "Assertion failed%s.\n%!" (position lexbuf) ;
        if interactive then Lexing.flush_input lexbuf else exit 1
    | e when not interactive ->
        Format.printf "Error in %s, line %d: %s\n"
          lexbuf.Lexing.lex_curr_p.Lexing.pos_fname
          lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
          (Printexc.to_string e) ;
        exit 1
    | System.Undefined s ->
        Format.printf "No definition found for %S !\n%!" s
    | System.Inconsistent_definition s ->
        Format.printf "Inconsistent extension of definition %S !\n" s
    | System.Arity_mismatch (s,a) ->
        Format.printf "Definition %S doesn't have arity %d !\n%!" s a
    | System.Interrupt ->
        Format.printf "User interruption.\n%!"
    | Prover.Level_inconsistency ->
        Format.printf "This formula cannot be handled by the left prover!\n%!"
    | Unify.NotLLambda t ->
        Format.printf "Not LLambda unification encountered: %a\n%!"
          Pprint.pp_term t
    | Invalid_command ->
        Format.printf "Invalid command, or wrong arity!\n%!"
    | Failure s ->
        Format.printf "Error: %s\n" s
    | e ->
        Format.printf "Unknown error: %s\n%!" (Printexc.to_string e)
  done with
  | Failure "eof" -> ()

and input_from_file file =
  let cwd = Sys.getcwd () in
  let lexbuf = Lexing.from_channel (open_in file) in
    Sys.chdir (Filename.dirname file) ;
    lexbuf.Lexing.lex_curr_p <- {
        lexbuf.Lexing.lex_curr_p with
          Lexing.pos_fname = file } ;
    input_defs lexbuf ;
    Sys.chdir cwd

and input_defs lexbuf = process Parser.input_def lexbuf
and input_queries ?(interactive=false) lexbuf =
  process ~interactive Parser.input_query lexbuf

and load_session () =
  System.reset_defs () ;
  List.iter input_from_file !session

and command lexbuf = function
  | "exit",[] -> exit 0
  | "help",[] -> Format.printf "%s" help_msg

  (* Session management *)
  | "include",[f] ->
      begin match Term.observe f with
        | Term.Var {Term.name=f} -> input_from_file f
        | _ -> raise Invalid_command
      end
  | "reset",[] -> session := [] ; load_session ()
  | "reload",[] -> load_session ()
  | "session",l ->
      session := List.map (fun f -> match Term.observe f with
                             | Term.Var {Term.name=f} -> f
                             | _ -> assert false) l ;
      load_session ()

  (* Turn debugging on/off. *)
  | "debug",[] -> System.debug := true
  | "debug",[d] ->
      System.debug :=
        begin match Term.observe d with
          | Term.Var {Term.name="on"}
          | Term.Var {Term.name="true"}  -> true
          | Term.Var {Term.name="off"}
          | Term.Var {Term.name="false"} -> false
          | _ -> raise Invalid_command
        end

  (* Turn timing on/off. *)
  | "time",[d] ->
      System.time :=
        begin match Term.observe d with
          | Term.Var {Term.name="on"}
          | Term.Var {Term.name="true"}  -> true
          | Term.Var {Term.name="off"}
          | Term.Var {Term.name="false"} -> false
          | _ -> raise Invalid_command
        end

  (* Print the contents of a table *)
  | "show_table",[p] ->
      begin match Term.observe p with
        | Term.Var {Term.name=name} -> System.show_table name
        | _ -> raise Invalid_command
      end

  (* Testing commands *)
  | "assert",[query] ->
      if !test then begin
        Format.printf "Checking that %a...\n%!" Pprint.pp_term query ;
        Term.reset_namespace () ;
        Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
          ~success:ignore ~failure:(fun () -> raise Assertion_failed)
      end
  | "assert_not",[query] ->
      if !test then begin
        Format.printf "Checking that %a is false...\n%!" Pprint.pp_term query ;
        Term.reset_namespace () ;
        Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
          ~success:(fun _ -> raise Assertion_failed) ~failure:ignore
      end
  | "assert_raise",[query] ->
      if !test then begin
        Format.printf "Checking that %a causes an error...\n%!"
          Pprint.pp_term query ;
        Term.reset_namespace () ;
        if
          try
            Prover.prove ~level:Prover.One ~local:0 ~timestamp:0 query
              ~success:ignore ~failure:ignore ;
            true
          with _ -> false
        then raise Assertion_failed
      end

  (* Experimental command, only taken into account in bedwyr programs
   * performing static analysis on .def files. *)
  | "type",_ -> ()

  | _ -> raise Invalid_command

let _ =
  load_session () ;
  List.iter (fun s -> input_queries (Lexing.from_string s)) !queries ;
  if !interactive then begin
    Format.printf "%s%!" welcome_msg ;
    input_queries ~interactive:true (Lexing.from_channel stdin)
  end
