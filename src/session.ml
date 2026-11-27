(****************************************************************************)
(* Copyright (C) 2013-2026 Inria (Institut National de Recherche            *)
(*                                en Informatique et en Automatique)        *)
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

open Extensions

type name_mode = [`relaxed | `warn | `strict]

type start_pos = {
  offset : int ;
  line : int ;
  bol : int ;
}

type outcome = {
  ok : bool ;
  messages : Json.t list ;
}

type command_chunk = {
  text : string ;
  start : start_pos ;
  end_line : int ;
  end_col : int ;
}

let system_message ~severity message : Json.t =
  `Assoc [
    "type", `String "system_message" ;
    "id", `Int (-1) ;
    "severity", `String severity ;
    "message", `String message ;
  ]

let is_thmod_path path =
  Filename.check_suffix path ".thmod"

let init
    ?(files = [])
    ?(strict = false)
    ?(name_mode = `relaxed)
    ?(thc_cache_limit = 64 * 1024 * 1024)
    ?(trust_compiled = true)
    ?(welcome = true)
    ~root
    () =
  try
    Checks.stratification_warnings_are_errors := strict ;
    Prover.strict_names := name_mode ;
    let file_kind = if is_thmod_path root then `thmod else `thm in
    State.reload Driver.initial_snapshot ;
    Driver.processing_state := Driver.Process_top ;
    State.Undo.set_enabled true ;
    State.Undo.reset () ;
    Driver.Setup.compiling := [] ;
    Accumulate.clear_specification_cache () ;
    Source.clear_virtual () ;
    Source.clear_thc_trust () ;
    Source.set_thc_cache_limit thc_cache_limit ;
    List.iter (fun (path, contents) -> Source.add_virtual path contents) files ;
    Driver.Setup.mode := `interactive ;
    Driver.Setup.file_kind := file_kind ;
    Driver.Setup.annotate := true ;
    Driver.Setup.recurse := false ;
    Driver.Setup.import_mode := `auto ;
    Driver.Setup.trust_compiled := trust_compiled ;
    Driver.Setup.input := root ;
    Driver.Setup.compiled := None ;
    Driver.Setup.unfinished := [] ;
    Driver.Setup.quiet := false ;
    Driver.Setup.print_interactions := false ;
    Driver.Setup.skip_to := None ;
    Driver.Setup.skip_reached := false ;
    Driver.Setup.stop_after_target := false ;
    Driver.Setup.state_at := None ;
    Output.collect_mode () ;
    ignore (Output.drain ()) ;
    if welcome then Output.msg_printf "%s" Driver.welcome_msg ;
    { ok = true ; messages = Output.drain () }
  with e ->
    { ok = false ;
      messages = [system_message ~severity:"error" (Printexc.to_string e)] }

let process ?start command =
  try
    let lb = Lexing.from_string command in
    begin match start with
    | None ->
        lb.Lexing.lex_curr_p <- {
          lb.Lexing.lex_curr_p with
          Lexing.pos_fname = !Driver.Setup.input ;
        }
    | Some { offset ; line ; bol } ->
        lb.Lexing.lex_curr_p <- {
          Lexing.pos_fname = !Driver.Setup.input ;
          pos_lnum = line ;
          pos_bol = bol ;
          pos_cnum = offset ;
        } ;
        (* The lexer engine recomputes pos_cnum as lex_abs_pos + the
           command-relative offset after every token. *)
        lb.Lexing.lex_abs_pos <- offset
    end ;
    Driver.Setup.lexbuf := lb ;
    let ok =
      try
        match Driver.process1 !Driver.processing_state with
        | Ok state ->
            Driver.processing_state := state ;
            true
        | Error _ -> false
      with
      | Driver.Setup.AbellaExit 0 -> true
      | Driver.Setup.AbellaExit _ -> false
      | e ->
          Output.msg_printf ~severity:Error "Error: %s" (sorry e) ;
          false
    in
    { ok ; messages = Output.drain () }
  with e ->
    let messages = Output.drain () in
    { ok = false ;
      messages = messages @ [system_message ~severity:"error" (sorry e)] }

let back count =
  if count <= 0 then { ok = true ; messages = [] }
  else
    try
      State.Undo.back count ;
      { ok = true ; messages = Output.drain () }
    with e ->
      let messages = Output.drain () in
      { ok = false ;
        messages = messages @ [system_message ~severity:"error" (sorry e)] }

let try_command ?start command =
  let snap = State.snapshot () in
  let undo = State.Undo.is_enabled () in
  Fun.protect
    ~finally:(fun () ->
      State.reload snap ;
      State.Undo.set_enabled undo)
    (fun () ->
      State.Undo.set_enabled false ;
      process ?start command)

let current_state () =
  match !Driver.istate with
  | None -> None
  | Some st -> Some (Prover.state_json st)

let current_display () = Driver.get_display ()

let in_proof () = !Driver.istate <> None

let split_commands ?(filename = "") content =
  let len = String.length content in
  let lb = Lexing.from_string content in
  Lexing.set_filename lb filename ;
  Lexer.comment_level := 0 ;
  let make_chunk (p1 : Lexing.position) (p2 : Lexing.position) =
    let off1 = max 0 (min len p1.pos_cnum) in
    let off2 = max off1 (min len p2.pos_cnum) in
    {
      text = String.sub content off1 (off2 - off1) ;
      start = {
        offset = off1 ;
        line = p1.pos_lnum ;
        bol = p1.pos_bol ;
      } ;
      end_line = p2.pos_lnum ;
      end_col = p2.pos_cnum - p2.pos_bol ;
    }
  in
  let eof_pos () =
    let p = lb.Lexing.lex_curr_p in
    { p with Lexing.pos_cnum = len }
  in
  let rec spin acc cmd_start =
    match Lexer.token lb with
    | Parser.EOF ->
        let acc =
          match cmd_start with
          | None -> acc
          | Some p1 -> make_chunk p1 (eof_pos ()) :: acc
        in
        List.rev acc
    | (Parser.BULLET _ | Parser.STAR | Parser.STARS _
      | Parser.PLUS | Parser.PLUSES _ | Parser.BACK | Parser.RESET)
      when cmd_start = None ->
        let chunk = make_chunk lb.Lexing.lex_start_p lb.Lexing.lex_curr_p in
        spin (chunk :: acc) None
    | Parser.DOT ->
        let p1 = match cmd_start with Some p -> p | None -> lb.Lexing.lex_start_p in
        let chunk = make_chunk p1 lb.Lexing.lex_curr_p in
        spin (chunk :: acc) None
    | _ ->
        let cmd_start =
          match cmd_start with
          | Some _ -> cmd_start
          | None -> Some lb.Lexing.lex_start_p
        in
        spin acc cmd_start
    | exception _ ->
        let p1 = match cmd_start with Some p -> p | None -> lb.Lexing.lex_start_p in
        let chunk = make_chunk p1 (eof_pos ()) in
        List.rev (chunk :: acc)
  in
  spin [] None
