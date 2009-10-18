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

open Term
open Metaterm
open Prover
open Types
open Typing
open Extensions
open Printf
open Debug

let can_read_specification = ref true

let interactive = ref true
let out = ref stdout
let compile_out = ref None

let switch_to_interactive = ref false
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

let position_range (p1, p2) =
  let file = p1.Lexing.pos_fname in
  let line = p1.Lexing.pos_lnum in
  let char1 = p1.Lexing.pos_cnum - p1.Lexing.pos_bol in
  let char2 = p2.Lexing.pos_cnum - p1.Lexing.pos_bol in
    if file = "" then
      ""
    else
      sprintf ": file %s, line %d, characters %d-%d" file line char1 char2


let lexbuf_from_file filename =
  let lexbuf = Lexing.from_channel (open_in filename) in
    lexbuf.Lexing.lex_curr_p <- {
      lexbuf.Lexing.lex_curr_p with
        Lexing.pos_fname = filename } ;
    lexbuf

let perform_switch_to_interactive () =
  assert !switch_to_interactive ;
  switch_to_interactive := false ;
  lexbuf := Lexing.from_channel stdin ;
  interactive := true ;
  out := stdout ;
  fprintf !out "Switching to interactive mode.\n%!"

let interactive_or_exit () =
  if not !interactive then
    if !switch_to_interactive then
      perform_switch_to_interactive ()
    else
      exit 1

let type_inference_error (pos, ct) exp act =
  eprintf "Typing error%s.\n%!" (position_range pos) ;
  match ct with
    | CArg ->
        eprintf "Expression has type %s but is used here with type %s\n%!"
          (ty_to_string act) (ty_to_string exp)
    | CFun ->
        eprintf "Expression is applied to too many arguments\n%!"


let read_specification name =
  fprintf !out "Reading specification %s\n%!" name ;
  let lexbuf_sig = lexbuf_from_file (name ^ ".sig") in
  let lexbuf_mod = lexbuf_from_file (name ^ ".mod") in
  let curr_lexbuf = ref lexbuf_sig in
    try
      Parser.lpsig Lexer.token lexbuf_sig ;
      curr_lexbuf := lexbuf_mod ;
      add_clauses (List.map type_uclause (Parser.lpmod Lexer.token lexbuf_mod))
    with
      | Parsing.Parse_error ->
          eprintf "Syntax error%s.\n%!" (position !curr_lexbuf) ;
          exit 1
      | TypeInferenceFailure(ci, exp, act) ->
          type_inference_error ci exp act ;
          exit 1
      | Failure s ->
          eprintf "Error: %s\n%!" s ;
          exit 1
      | e ->
          eprintf "Unknown error: %s\n%!" (Printexc.to_string e) ;
          exit 1


(* Checks *)

let ensure_no_restrictions term =
  if get_max_restriction term > 0 then
    failwith "Cannot use restrictions: *, @ or +"

let untyped_ensure_no_restrictions term =
  ensure_no_restrictions (umetaterm_to_metaterm [] term)

let warn_stratify names term =
  let rec aux nested term =
    match term with
      | Pred(p, _) when nested && List.mem (term_head_name p) names -> true
      | Arrow(left, right) -> aux true left || aux nested right
      | Binding(_, _, body) -> aux nested body
      | Or(left, right) -> aux nested left || aux nested right
      | And(left, right) -> aux nested left || aux nested right
      | _ -> false
  in
    if aux false term then
      fprintf !out "Warning: Definition might not be stratified%!"

let check_theorem thm =
  ensure_no_restrictions thm

let ensure_not_capital name =
  if is_capital_name name then
    failwith (sprintf "Defined predicates may not begin with \
                       a capital letter.")

let ensure_name_contained id ids =
  if not (List.mem id ids) then
    failwith ("Found stray clause for " ^ id)

let check_defs names defs =
  List.iter ensure_not_capital names ;
  List.iter
    (fun (head, body) ->
       ensure_name_contained (def_head_name head) names ;
       ensure_no_restrictions head ;
       ensure_no_restrictions body ;
       warn_stratify names body)
    defs


(* Compilation and importing *)

let marshal citem =
  match !compile_out with
    | Some cout -> Marshal.to_channel cout citem []
    | None -> ()

let ensure_finalized_specification () =
  if !can_read_specification then begin
    can_read_specification := false ;
    marshal ktable ;
    marshal ctable ;
    marshal !clauses
  end

let compile citem =
  ensure_finalized_specification () ;
  marshal citem

let verify_signature file =
  let imported_ktable = (Marshal.from_channel file : ktable) in
  let imported_ctable = (Marshal.from_channel file : ctable) in
  let imported_clauses = (Marshal.from_channel file : clauses) in
    ktable = imported_ktable &&
      ctable = imported_ctable &&
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
                    add_lemma name thm ;
                | CDefine(idtys, defs) ->
                    add_consts idtys ;
                    let ids = List.map fst idtys in
                      check_defs ids defs ;
                      add_defs ids Inductive defs ;
                | CCoDefine(idtys, defs) ->
                    add_consts idtys ;
                    let ids = List.map fst idtys in
                      check_defs ids defs ;
                      add_defs ids CoInductive defs
                | CImport(filename) ->
                    import filename
                | CKind(ids) ->
                    add_types ids
                | CType(ids, ty) ->
                    add_consts (List.map (fun id -> (id, ty)) ids)
            done
          else
            failwith ("Import failed: " ^ filename ^
                        " was compiled with a different specification" )
        with End_of_file -> ()
    else
      fprintf !out "Ignoring import: %s has already been imported.\n%!"
        filename


(* Proof processing *)

let query q =
  let fv = ids_to_fresh_tyctx (umetaterm_extract_if is_capital_name q) in
  let ctx = fresh_alist ~tag:Logic ~used:[] fv in
  match type_umetaterm ~ctx (UBinding(Metaterm.Exists, fv, q)) with
    | Binding(Metaterm.Exists, fv, q) ->
        let ctx = fresh_alist ~tag:Logic ~used:[] fv in
        let q = replace_metaterm_vars ctx q in
        let _ = Tactics.search
          ~depth:max_int
          ~hyps:[]
          ~clauses:!clauses
          ~alldefs:(defs_table_to_list ())
          ~sc:(fun () ->
                 fprintf !out "Found solution:\n" ;
                 List.iter
                   (fun (n, v) ->
                      fprintf !out "%s = %s\n" n (term_to_string v))
                   ctx ;
                 fprintf !out "\n%!")
          q
        in
          fprintf !out "No more solutions.\n%!"
    | _ -> assert false

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
              untyped_ensure_no_restrictions t ;
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
          interactive_or_exit ()
      | End_of_file ->
          if !switch_to_interactive then
            perform_switch_to_interactive ()
          else begin
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
          interactive_or_exit () ;
      | TypeInferenceFailure(ci, exp, act) ->
          type_inference_error ci exp act ;
          interactive_or_exit ()
      | e ->
          eprintf "Error: %s\n%!" (Printexc.to_string e) ;
          interactive_or_exit ()
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
            let thm = type_umetaterm thm in
              check_theorem thm ;
              theorem thm ;
              begin try
                process_proof name ;
                compile (CTheorem(name, thm)) ;
                add_lemma name thm ;
              with AbortProof -> () end
        | Define(idtys, udefs) ->
            add_consts idtys ;
            let defs = type_udefs udefs in
            let ids = List.map fst idtys in
              check_defs ids defs ;
              compile (CDefine(idtys, defs)) ;
              add_defs ids Inductive defs
        | CoDefine(idtys, udefs) ->
            add_consts idtys ;
            let defs = type_udefs udefs in
            let ids = List.map fst idtys in
              check_defs ids defs ;
              compile (CCoDefine(idtys, defs)) ;
              add_defs ids CoInductive defs
        | TopSet(k, v) ->
            set k v
        | Import(filename) ->
            compile (CImport filename) ;
            import filename ;
        | Specification(filename) ->
            if !can_read_specification then begin
              read_specification filename ;
              ensure_finalized_specification ()
            end else
              failwith ("Specification can only be read " ^
                          "at the begining of a development.")
        | Query(q) -> query q
        | Kind(ids) ->
            compile (CKind ids)
        | Type(ids, ty) ->
            compile (CType(ids, ty))
      end ;
      if !interactive then flush stdout ;
      if !annotate then fprintf !out "</pre>%!" ;
      fprintf !out "\n%!" ;
  with
    | Failure "lexing: empty token" ->
        eprintf "Unknown symbol" ;
        exit (if !interactive then 0 else 1)
    | Failure s ->
        eprintf "Error: %s\n%!" s ;
        interactive_or_exit ()
    | End_of_file ->
        if !switch_to_interactive then
          perform_switch_to_interactive ()
        else begin
          fprintf !out "Goodbye.\n%!" ;
          ensure_finalized_specification () ;
          if !annotate then fprintf !out "</pre>\n%!" ;
          exit 0
        end
    | Parsing.Parse_error ->
        eprintf "Syntax error%s.\n%!" (position !lexbuf) ;
        Lexing.flush_input !lexbuf ;
        interactive_or_exit ()
    | TypeInferenceFailure(ci, exp, act) ->
        type_inference_error ci exp act ;
        interactive_or_exit ()
    | e ->
        eprintf "Unknown error: %s\n%!" (Printexc.to_string e) ;
        interactive_or_exit ()
  done with
  | Failure "eof" -> ()


(* Command line and startup *)

let welcome_msg = sprintf "Welcome to Abella %s\n" Version.version

let usage_message = "abella [options] <theorem-file>"

let set_output filename =
  out := open_out filename

let set_compile_out filename =
  compile_out := Some (open_out_bin filename)

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

let set_input filename =
  if !interactive then begin
    interactive := false ;
    lexbuf := lexbuf_from_file filename
  end else begin
    let file = !lexbuf.Lexing.lex_curr_p.Lexing.pos_fname in
      eprintf "Error: Input set to %s, but found additional input %s."
        file filename ;
      exit 1
  end

let _ =
  Arg.parse options set_input usage_message ;
  fprintf !out "%s%!" welcome_msg ;
  process ()
