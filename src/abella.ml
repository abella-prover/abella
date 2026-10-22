(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2022 Inria (Institut National de Recherche            *)
(*                         en Informatique et en Automatique)               *)
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
open Abella_driver
open Abella_types
open Extensions

let set_output filename =
  Output.dest := Channel (open_out_bin filename)

let set_or_exit k v =
  try set k v with
  | Failure msg ->
      Output.msg_printf ~severity:Error "Error: %s" msg ;
      raise @@ AbellaExit 1

let abella_main flags switch output compiled annotate norec _em verb infile =
  try begin
    Output.set_verbosity verb ;
    List.iter (fun (k, v) -> set_or_exit k v) flags ;
    if switch then Setup.mode := `switch ;
    Option.iter set_output output ;
    if annotate then Output.annotation_mode () ;
    Setup.annotate := annotate ;
    Setup.recurse := not norec ;
    begin match infile with
    | Some file -> begin
        let module Thm = (val Source.read_thm ?thc:compiled file) in
        Setup.compiled := Some (module Thm) ;
        Setup.mode := if switch then `switch else `batch ;
        Setup.lexbuf := Thm.lex true ;
        Setup.input := Filename.concat (Option.value Thm.dir ~default:"") "<dummy>.thm"
      end
    | None ->
        Setup.lexbuf := Lexing.from_channel ~with_positions:false stdin
    end ;
    if !Setup.mode = `interactive then
      Output.msg_printf "%s" welcome_msg ;
    State.Undo.set_enabled (!Setup.mode <> `batch) ;
    while true do ignore (process1 ()) done ; 0
  end with
  | AbellaExit n -> n
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
  Sys.set_signal Sys.sigint
    (Sys.Signal_handle (fun _ -> raise UserInterrupt)) ;

  let open Cmdliner in

  let flag_conv : (string * set_value) list Arg.conv =
    let parse str =
      try
        Lexing.from_string str |>
        Parser.cmdline_flags Lexer.token |>
        Result.ok
      with
      | Abella_types.Reported_parse_error
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
    let doc = "Switch to interactive mode after processing input." in
    Arg.(value @@ flag @@ info ["i"] ~doc)
  in

  let output =
    let doc = "Save all output to $(docv)." in
    Arg.(value @@ opt (some string) None @@
         info ["o" ; "output"] ~doc ~docv:"FILE")
  in

  let compiled =
    let doc = "Save compiled Abella development to $(docv) instead of the \
               default location. By default, in batch mode, the compiled version \
               of $(i,file.thm) is saved to $(i,file.thc), while in interactive \
               mode the compiled development is not saved anywhere." in
    Arg.(value @@ opt (some string) None @@
         info ["c" ; "compile"] ~doc ~docv:"FILE")
  in

  let annotate =
    let doc = "Annotation mode: change Abella output to JSON format." in
    Arg.(value @@ flag @@ info ["a" ; "annotate"] ~doc)
  in

  let norec =
    let doc = "Do not recursively invoke Abella for imports." in
    Arg.(value @@ flag @@ info ["N" ; "non-recursive"] ~doc)
  in

  let em =
    let doc = "Does nothing; use abella_dep instead." in
    let deprecated = "The -M flag is deprecated and does nothing; use abella_dep instead" in
    Arg.(value @@ flag @@ info ["M"] ~doc ~deprecated)
  in

  let verb =
    let doc = "Set verbosity to $(docv)." in
    Arg.(value @@ opt int 0 @@
         info ["verbosity"] ~doc ~docv:"NUM")
  in

  let file =
    let doc = "An Abella development to process in batch mode. \
               The $(docv) must end with the extension $(b,.thm). \
               If no $(docv) is provided, Abella runs in interactive mode." in
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
    Cmd.v info @@ Term.(const abella_main $ flags $ switch $ output $ compiled $ annotate $ norec $ em $ verb $ file)
  in

  Stdlib.exit (Cmd.eval' cmd)
;;
