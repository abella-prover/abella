(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Run "abella -a" on all examples *)

let rec thmfiles dir =
  let process f =
    let f = Filename.concat dir f in
    if Sys.is_directory f then
      thmfiles f
    else if Filename.check_suffix f ".thm" then
      Seq.return f
    else
      Seq.empty
  in
  let fs = Sys.readdir dir in
  Array.fast_sort String.compare fs ;
  Array.map process fs
  |> Array.fold_left Seq.append Seq.empty
;;

let () =
  if not !Sys.interactive && Sys.unix then begin
    let files = thmfiles "../../../examples" in
    let buf = Buffer.create 19 in
    let open Format in
    let ff = formatter_of_buffer buf in
    fprintf ff ".PHONY: all\nall:\n\n" ;
    let rec loop fs =
      match fs () with
      | Seq.Nil -> ()
      | Seq.Cons (thmfile, fs) ->
          let jsonfile = String.map (function '/' | '.' -> '_' | c -> c) thmfile ^ ".json" in
          fprintf ff "%s: %s\n" jsonfile thmfile ;
          fprintf ff "\t../src/abella.exe -a $< -o $@@\n" ;
          fprintf ff "all: %s\n" jsonfile ;
          loop fs
    in
    loop files ;
    let (mkfilename, mkfilech) =
      Filename.open_temp_file ~mode:[Open_binary] "Makefile" "examples" in
    Buffer.output_buffer mkfilech buf ;
    close_out mkfilech ;
    Printf.printf "make -f %s -j\n" mkfilename ;
    Unix.execvp "make" [| "make" ; "-f" ; mkfilename ; "-j" |]
  end
;;
