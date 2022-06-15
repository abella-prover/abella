(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Run "abella -a" on all examples *)

let () =
  if not !Sys.interactive && Sys.unix then begin
    let ch = Unix.open_process_args_in "git"
        [| "git" ; "ls-files" ; "../../../examples/**.thm" |] in
    let buf = Buffer.create 19 in
    let open Format in
    let ff = formatter_of_buffer buf in
    fprintf ff ".PHONY: all\nall:\n\n" ;
    let rec loop () =
      match In_channel.input_line ch with
      | Some thmfile ->
          let jsonfile = String.map (function '/' | '.' -> '_' | c -> c) thmfile ^ ".json" in
          fprintf ff "%s: %s\n" jsonfile thmfile ;
          fprintf ff "\t../src/abella.exe -a $< -o $@@\n" ;
          fprintf ff "all: %s\n" jsonfile ;
          loop ()
      | None ->
          close_in ch
    in
    loop () ;
    pp_print_flush ff () ;
    let (mkfilename, mkfilech) =
      Filename.open_temp_file ~mode:[Open_binary] "Makefile" "examples" in
    Buffer.output_buffer mkfilech buf ;
    close_out mkfilech ;
    Printf.printf "make -f %s -j\n" mkfilename ;
    Unix.execvp "make" [| "make" ; "-f" ; mkfilename ; "-j" |]
  end
;;
