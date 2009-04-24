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
open Debug

let can_read_specification = ref true
let last_sig = ref ("", 0)

let interactive = ref true
let out = ref stdout
let compile_out = ref None

type source = File of string | Stdin
let sources = Queue.create ()
let lexbuf = ref (Lexing.from_channel stdin)

let annotate = ref false
let count = ref 0

exception AbortProof


(* Input *)

let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  let char = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    if file = "" then
      "" (* lexbuf information is rarely accurate at the toplevel *)
    else
      sprintf ": file %s, line %d, character %d" file line char

let lexbuf_from_file filename =
  let lexbuf = Lexing.from_channel (open_in filename) in
    lexbuf.Lexing.lex_curr_p <- {
      lexbuf.Lexing.lex_curr_p with
        Lexing.pos_fname = filename } ;
    lexbuf

let is_next_source () =
  not (Queue.is_empty sources)

let next_source () =
  match Queue.take sources with
    | File filename ->
        lexbuf := lexbuf_from_file filename ;
        interactive := false
    | Stdin ->
        lexbuf := Lexing.from_channel stdin ;
        interactive := true ;
        out := stdout ;
        fprintf !out "Switching to interactive mode.\n%!"

let parse_mod_file name =
  fprintf !out "Reading clauses from %s\n%!" name ;
  let lexbuf = lexbuf_from_file name in
    try
      add_clauses (Parser.clauses Lexer.token lexbuf)
    with
      | Parsing.Parse_error ->
          eprintf "Syntax error%s.\n%!" (position lexbuf) ;
          exit 1


(* Checks *)

let ensure_no_restrictions term =
  if get_max_restriction term > 0 then
    failwith "Cannot use restrictions: *, @ or +"

let ensure_no_free_vars free_vars =
  if free_vars <> [] then
    failwith (sprintf "Unbound variables: %s%!"
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
      fprintf !out "Warning: %s might not be stratified%!" (sig_to_string dsig)
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


(* Compilation and importing *)

let marshal citem =
  match !compile_out with
    | Some cout -> Marshal.to_channel cout citem []
    | None -> ()

let ensure_finalized_specification () =
  if !can_read_specification then begin
    can_read_specification := false ;
    marshal !clauses
  end

let compile citem =
  ensure_finalized_specification () ;
  marshal citem

let verify_signature file =
  let imported_clauses = (Marshal.from_channel file : clauses) in
    !clauses = imported_clauses

let imported = ref []

let rec import filename =
  let filename = filename ^ ".thc" in
    if not (List.mem filename !imported) then
      let file = open_in_bin filename in
        imported := filename :: !imported ;
        try
          fprintf !out "Importing definitions and theorems from %s\n%!"
            filename ;
          if verify_signature file then
            while true do
              match (Marshal.from_channel file : compiled) with
                | CTheorem(name, thm) ->
                    check_theorem thm ;
                    add_lemma name thm ;
                    last_sig := ("", 0)
                | CDefine(def) ->
                    check_def def ;
                    add_def Inductive def
                | CCoDefine(def) ->
                    check_def def ;
                    add_def CoInductive def
                | CImport(filename) ->
                    import filename
            done
          else
            failwith ("Import failed: " ^ filename ^
                        " was compiled with a different specification" )
        with End_of_file -> ()
    else
      fprintf !out "Ignoring import: %s has already been imported.\n%!"
        filename


(* Proof processing *)

let set k v =
  match k, v with
    | "subgoals", Int d when d >= 0 -> subgoal_depth := d
    | "subgoals", Str "on" -> subgoal_depth := 1000
    | "subgoals", Str "off" -> subgoal_depth := 0
    | "subgoals", _ ->
        failwith ("Unknown value '" ^ (set_value_to_string v) ^
                    "' for key 'subgoals'." ^
                    " Expected 'on', 'off', or non-negative integer.")

    | "debug", Str "on" -> debug_level := 1
    | "debug", Str "off" -> debug_level := 0
    | "debug", _ ->
        failwith ("Unknown value '" ^ (set_value_to_string v) ^
                    "' for key 'debug'." ^
                    " Expected 'on' or 'off'.")

    | _, _ -> failwith ("Unknown key '" ^ k ^ "'.")

let rec process_proof name =
  let finished = ref false in
    try while not !finished do try
      if !annotate then begin
        fprintf !out "</pre>\n%!" ;
        incr count ;
        fprintf !out "<a name=\"%d\"></a>\n%!" !count ;
        fprintf !out "<pre>\n%!"
      end ;
      display !out ;
      fprintf !out "%s < %!" name ;
      let input = Parser.command Lexer.token !lexbuf in
        if not !interactive then begin
          let pre, post = if !annotate then "<b>", "</b>" else "", "" in
            fprintf !out "%s%s.%s\n%!" pre (command_to_string input) post
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
          | Abbrev(h, s) -> abbrev h s
          | Unabbrev(hs) -> unabbrev hs
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
          | Set(k, v) -> set k v
        end ;
        if !interactive then flush stdout ;
    with
      | Failure "lexing: empty token" ->
          exit (if !interactive then 0 else 1)
      | Failure "Proof completed." ->
          fprintf !out "Proof completed.\n%!" ;
          reset_prover () ;
          finished := true
      | Failure s ->
          eprintf "Error: %s\n%!" s ;
          if not !interactive then exit 1
      | End_of_file ->
          if is_next_source () then begin
            next_source () ;
            process_proof name ;
            finished := true
          end else begin
            fprintf !out "Proof NOT completed.\n%!" ;
            exit 1
          end
      | AbortProof ->
          fprintf !out "Proof aborted.\n%!" ;
          reset_prover () ;
          raise AbortProof
      | Parsing.Parse_error ->
          eprintf "Syntax error%s.\n%!" (position !lexbuf) ;
          Lexing.flush_input !lexbuf ;
          if not !interactive then exit 1
      | e ->
          eprintf "Error: %s\n%!" (Printexc.to_string e) ;
          if not !interactive then exit 1
    done with
      | Failure "eof" -> ()

let rec process () =
  try while true do try
    if !annotate then begin
      incr count ;
      fprintf !out "<a name=\"%d\"></a>\n%!" !count ;
      fprintf !out "<pre class=\"code\">\n%!"
    end ;
    fprintf !out "Abella < %!" ;
    let input = Parser.top_command Lexer.token !lexbuf in
      if not !interactive then begin
          let pre, post = if !annotate then "<b>", "</b>" else "", "" in
            fprintf !out "%s%s.%s\n%!" pre (top_command_to_string input) post
      end ;
      begin match input with
        | Theorem(name, thm) ->
            check_theorem thm ;
            theorem thm ;
            begin try
              process_proof name ;
              compile (CTheorem(name, thm)) ;
              add_lemma name thm ;
              last_sig := ("", 0)
            with AbortProof -> () end
        | Define(def) ->
            check_def def ;
            compile (CDefine def) ;
            add_def Inductive def
        | CoDefine(def) ->
            check_def def ;
            compile (CCoDefine def) ;
            add_def CoInductive def
        | TopSet(k, v) ->
            set k v
        | Import(filename) ->
            compile (CImport filename) ;
            last_sig := ("", 0) ;
            import filename ;
            last_sig := ("", 0)
        | Specification(filename) ->
            if !can_read_specification then begin
              parse_mod_file (filename ^ ".mod") ;
              ensure_finalized_specification ()
            end else
              failwith ("Specification can only be read " ^
                          "at the begining of a development.")
      end ;
      if !interactive then flush stdout ;
      if !annotate then fprintf !out "</pre>%!" ;
      fprintf !out "\n%!" ;
  with
    | Failure "lexing: empty token" ->
        exit (if !interactive then 0 else 1)
    | Failure s ->
        eprintf "Error: %s\n%!" s ;
        if not !interactive then exit 1
    | End_of_file ->
        if is_next_source () then begin
          next_source () ;
          process ()
        end else begin
          fprintf !out "Goodbye.\n%!" ;
          ensure_finalized_specification () ;
          if !annotate then fprintf !out "</pre>\n%!" ;
          exit 0
        end
    | Parsing.Parse_error ->
        eprintf "Syntax error%s.\n%!" (position !lexbuf) ;
        Lexing.flush_input !lexbuf ;
        if not !interactive then exit 1
    | e ->
        eprintf "Unknown error: %s\n%!" (Printexc.to_string e) ;
        if not !interactive then exit 1
  done with
  | Failure "eof" -> ()


(* Command line and startup *)

let welcome_msg = sprintf "Welcome to Abella %s\n" Version.version

let usage_message = "abella [options] <theorem-file>"

let set_output filename =
  out := open_out filename

let set_compile_out filename =
  compile_out := Some (open_out_bin filename)

let switch_to_interactive = ref false

let options =
  Arg.align
    [
      ("-i", Arg.Set switch_to_interactive,
       " Switch to interactive mode after reading inputs") ;
      ("-o", Arg.String set_output,
       "<file-name> Output to file") ;
      ("-c", Arg.String set_compile_out,
       "<file-name> Compile definitions and theorems in an importable format") ;
      ("-a", Arg.Set annotate, " Annotate mode") ;
    ]

let add_input filename =
  Queue.add (File filename) sources

let _ =
  Arg.parse options add_input usage_message ;
  if !switch_to_interactive or Queue.is_empty sources then
    Queue.add Stdin sources ;
  next_source () ;
  fprintf !out "%s%!" welcome_msg ;
  process ()
