(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2022 Inria (Institut National de Recherche            *)
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

(* Command line and startup *)

open Abella_lib
open Driver
open Types
open Extensions

let set_output filename =
  Output.dest := Channel (open_out_bin filename)

let set_or_exit k v =
  try set k v with
  | Failure msg ->
      Output.msg_printf ~severity:Error "Error: %s" msg ;
      raise @@ Setup.AbellaExit 1

let abella_main
    flags _switch output _compiled annotate norec strict_stratification
    warn_names strict_names strict _em verb print_inter quiet skip only
    state_at infile =
  try begin
    Output.set_verbosity verb ;
    Checks.stratification_warnings_are_errors :=
      strict_stratification || strict ;
    Prover.strict_names :=
      if strict_names || strict then `strict
      else if warn_names then `warn
      else `relaxed ;
    List.iter (fun (k, v) -> set_or_exit k v) flags ;
    Option.iter set_output output ;
    if annotate then Output.annotation_mode () ;
    Setup.annotate := annotate ;
    Setup.recurse := not norec ;
    Setup.print_interactions := print_inter ;
    Setup.quiet := quiet ;
    Setup.skip_reached := false ;
    Setup.stop_after_target := false ;
    Setup.state_at := None ;
    begin match skip, only with
    | Some _, Some _ ->
        Output.msg_printf ~severity:Error
          "Error: --skip and --only cannot be used together" ;
        raise @@ Setup.AbellaExit 1
    | Some s, None -> begin
        let s = String.trim s in
        match int_of_string_opt s with
        | Some n ->
            if n < 1 then begin
              Output.msg_printf ~severity:Error
                "Error: --skip argument must be >= 1" ;
              raise @@ Setup.AbellaExit 1
            end ;
            Setup.skip_to := Some (Setup.Skip_line n)
        | None ->
            if s = "" then begin
              Output.msg_printf ~severity:Error
                "Error: --skip argument must be a line number \
                 or a theorem name" ;
              raise @@ Setup.AbellaExit 1
            end ;
            Setup.skip_to := Some (Setup.Skip_theorem s)
      end
    | None, Some s ->
        let s = String.trim s in
        if s = "" then begin
          Output.msg_printf ~severity:Error
            "Error: --only argument must be a theorem name" ;
          raise @@ Setup.AbellaExit 1
        end ;
        Setup.skip_to := Some (Setup.Skip_theorem s) ;
        Setup.stop_after_target := true
    | None, None ->
        Setup.skip_to := None
    end ;
    begin match state_at with
    | None -> ()
    | Some n ->
        if n < 1 then begin
          Output.msg_printf ~severity:Error
            "Error: --state-at argument must be >= 1" ;
          raise @@ Setup.AbellaExit 1
        end ;
        Setup.state_at := Some n
    end ;
    begin match infile with
    | Some file -> begin
        let is_thmod = Filename.check_suffix file ".thmod" in
        let module Src =
          (val if is_thmod then
                 Thmod.read file
               else
                 Thm.read file)
        in
        Setup.compiled := Some (module Src) ;
        Setup.file_kind := if is_thmod then `thmod else `thm ;
        Setup.mode := `batch ;
        Setup.lexbuf := Src.lex true ;
        Setup.input := Src.path
      end
    | None ->
        Setup.lexbuf := Lexing.from_channel ~with_positions:false stdin
    end ;
    if !Setup.mode = `interactive then
      Output.msg_printf "%s" welcome_msg ;
    State.Undo.set_enabled (!Setup.mode <> `batch) ;
    let state = ref Driver.Process_top in
    while true do
      match process1 !state with
      | Ok next -> state := next
      | Error _ -> ()
    done ; 0
  end with
  | Setup.AbellaExit n -> Output.flush () ; n
  | e ->
      let msg = match e with
        | Failure msg -> "Failure: " ^ msg
        | Unix.Unix_error (err, fn, arg) ->
            Printf.sprintf "System error: %s(%s): %s"
              fn arg (Unix.error_message err)
        | _ -> Printf.sprintf "Error: %s" (sorry e)
      in
      Output.msg_printf ~severity:Error "%s" msg ;
      Output.flush () ; 1

let () =
  if Sys.getenv_opt "ABELLA_GC_STATS" <> None then
    at_exit (fun () ->
        let s = Gc.stat () in
        Printf.eprintf
          "gc-stats: minor_words=%.0f major_words=%.0f minor_collections=%d major_collections=%d compactions=%d\n%!"
          s.Gc.minor_words s.Gc.major_words
          s.Gc.minor_collections s.Gc.major_collections s.Gc.compactions) ;
  Sys.set_signal Sys.sigint
    (Sys.Signal_handle (fun _ -> raise Setup.UserInterrupt)) ;

  let open Cmdliner in

  let flag_conv : (string * set_value) list Arg.conv =
    let parse str =
      try
        Lexing.from_string str |>
        Parser.cmdline_flags Lexer.token |>
        Result.ok
      with
      | Types.Reported_parse_error
      | Parser.Error ->
          Printf.ksprintf (fun s -> `Msg s)
            "Could not parse argument: %S" str
          |> Result.error
    in
    let print _ _ = () in
    Arg.conv (parse, print)
  in

  let flags =
    let doc = "Intialize Abella flags based on $(docv), which is a \
               comma-separated list of key=value pairs. Unknown \
               flags are silently ignored." in
    Arg.(value @@ opt flag_conv [] @@
         info ["f" ; "flags"] ~doc ~docv:"FLAGS")
  in

  let switch =
    let deprecated =
      "The -i flag is deprecated and does nothing; use a frontend such \
       as Abella Web for interactive sessions." in
    Arg.(value @@ flag @@ info ["i"] ~deprecated)
  in

  let output =
    let doc = "Save all output to $(docv)." in
    Arg.(value @@ opt (some string) None @@
         info ["o" ; "output"] ~doc ~docv:"FILE")
  in

  let compiled =
    let deprecated =
      "Choosing the compiled location is no longer allowed." in
    Arg.(value @@ opt (some string) None @@
         info ["c" ; "compile"] ~docv:"FILE" ~deprecated)
  in

  let annotate =
    let doc = "Annotation mode: change Abella output to JSON format." in
    Arg.(value @@ flag @@ info ["a" ; "annotate"] ~doc)
  in

  let norec =
    let doc = "Do not recursively invoke Abella for imports." in
    Arg.(value @@ flag @@ info ["N" ; "non-recursive"] ~doc)
  in

  let strict_stratification =
    let doc = "Stratification failures are errors." in
    Arg.(value @@ flag @@ info ["strict-stratification"] ~doc)
  in

  let warn_names =
    let doc = "Warn when a proof refers to a hypothesis or variable whose \
               name was not supplied by the user." in
    Arg.(value @@ flag @@ info ["warn-names"] ~doc)
  in

  let strict_names =
    let doc = "Treat references to system-generated names as errors." in
    Arg.(value @@ flag @@ info ["strict-names"] ~doc)
  in

  let strict =
    let doc = "Synonym for --strict-names --strict-stratification." in
    Arg.(value @@ flag @@ info ["strict"] ~doc)
  in

  let em =
    let deprecated =
      "The -M flag is deprecated and does nothing; use abella_dep instead." in
    Arg.(value @@ flag @@ info ["M"] ~deprecated)
  in

  let verb =
    let doc = "Set verbosity to $(docv)." in
    Arg.(value @@ opt int 0 @@
         info ["verbosity"] ~doc ~docv:"NUM")
  in

  let print_inter =
    let doc = "In batch mode, print the sequents after every proof tactic, \
               like in interactive mode." in
    Arg.(value @@ flag @@ info ["print-interactions"] ~doc)
  in

  let quiet =
    let doc = "In batch mode, suppress echoing commands and progress messages." in
    Arg.(value @@ flag @@ info ["q" ; "quiet"] ~doc)
  in

  let skip =
    let doc = "Start processing proof commands from $(docv) onwards. If \
               $(docv) is a number, it is the line to start from: earlier \
               proof commands are accepted as no-ops and earlier theorems \
               are accepted as true, and it is an error if the line is in \
               the middle of a proof. If $(docv) is the name of a theorem, \
               checking starts from the first theorem with that name; it \
               is an error if no such theorem exists." in
    Arg.(value @@ opt (some string) None @@
         info ["skip"] ~doc ~docv:"WHERE")
  in

  let only =
    let doc = "Like $(b,--skip)=$(docv), but stop and exit after checking \
               the named theorem." in
    Arg.(value @@ opt (some string) None @@
         info ["only"] ~doc ~docv:"THEOREM")
  in

  let state_at =
    let doc = "In batch mode, print the proof state at line $(docv) and exit." in
    Arg.(value @@ opt (some int) None @@
         info ["state-at"] ~doc ~docv:"LINE")
  in

  let file =
    let doc = "An Abella development to process in batch mode. \
               The $(docv) must end with the extension $(b,.thm) or \
               $(b,.thmod). If no $(docv) is provided, Abella runs in \
               interactive mode." in
    Arg.(value @@ pos 0 (some string) None @@
         info [] ~docv:"FILE" ~doc)
  in

  let cmd =
    let doc = "Run Abella in batch or interactive mode." in
    let man = [
      `S Manpage.s_see_also ;
      `P "$(b,abella_dep)(1), $(b,abella_doc)(1)" ;
      `S Manpage.s_bugs ;
      `P "File bug reports at <$(b,https://github.com/abella-prover/abella/issues)>" ;
    ] in
    let info = Cmd.info "abella" ~doc ~man ~exits:[] ~version:Version.version in
    Cmd.v info @@
    Term.(const abella_main $ flags $ switch $ output $ compiled $
          annotate $ norec $ strict_stratification $ warn_names $
          strict_names $ strict $ em $ verb $ print_inter $ quiet $
          skip $ only $ state_at $ file)
  in

  Stdlib.exit (Cmd.eval' cmd)
;;
