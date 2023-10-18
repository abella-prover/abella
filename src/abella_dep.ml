(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2023  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Dependency generator for Abella *)

open Extensions

let abella = ref "abella"
let makefile = ref "Makefile"
let noclobber = ref false
let recursive = ref false

let options = Arg.[
    "-a", Set_string abella,
    Printf.sprintf "CMD Set the ABella command to CMD (Default: %s)" !abella ;
    "-o", Set_string makefile,
    Printf.sprintf "FILE Output dependencies to FILE (default: %s)" !makefile ;
    "-nc", Set noclobber, " Do not clobber an existing Makefile (default: false)" ;
    "-r", Set recursive, " Process directories recursively (default: false)" ;
  ] |> Arg.align

let dep_tab : (string, string list option) Hashtbl.t = Hashtbl.create 19

let rec add_input_file file =
  match Unix.stat file with
  | { st_kind = S_DIR ; _ } when !recursive -> begin
      let dir = file in
      let fs = Sys.readdir dir in
      Array.fast_sort String.compare fs ;
      Array.iter begin fun file ->
        let file = Filename.concat dir file in
        add_input_file file
      end fs
    end
  | { st_kind = S_REG ; _ } when Filename.check_suffix file ".thm" -> begin
      let thmfile = file in
      match Hashtbl.find dep_tab thmfile with
      | None ->
          failwithf "Circular dependencies detected for %S" thmfile
      | Some _ -> ()
      | exception Not_found -> begin
          let base = Filename.chop_suffix thmfile ".thm" in
          let thcfile = base ^ ".thc" in
          Hashtbl.replace dep_tab thcfile None ;
          let (specs, deps) = Depend.thm_dependencies base in
          let deps = List.map (fun f -> f ^ ".thc") deps in
          let deps = specs @ deps in
          Hashtbl.replace dep_tab thcfile (Some deps)
        end
    end
  | { st_kind = S_REG ; _ } ->
      if not !recursive then
        failwithf "Illegal file %S; input files must have suffix .thm" file ;
  | _ ->
      failwithf "Cannot process: %s" file

let usage_message =
  Printf.sprintf "Usage: %s [options] [<theorem-file> | <directory>] ..."
    (if !Sys.interactive then "abella_dep" else Sys.argv.(0))

let main () =
  Arg.parse options add_input_file usage_message ;
  if !noclobber && Sys.file_exists !makefile then
    failwithf "Would clobber %S but given option -nc" !makefile ;
  let out = match !makefile with
    | "-" -> stdout
    | f -> open_out_bin f
  in
  Printf.fprintf out ".PHONY: all\n" ;
  Printf.fprintf out "%%.thc: %%.thm\n" ;
  Printf.fprintf out "\t%s -nr -c $@ -o ${<:%%.thm=%%.out} $<\n" !abella ;
  Hashtbl.iter begin fun file deps ->
    if not @@ Filename.check_suffix file ".thc" then () else
    Printf.fprintf out "all: %s\n" file ;
    match deps with
    | None ->
        failwithf "BUG: incomplete dependencies for %S" file
    | Some deps ->
        if deps = [] then () else
        let deps = String.concat " " deps in
        Printf.fprintf out "%s: %s\n" file deps
  end dep_tab ;
  close_out out

let () =
  if not !Sys.interactive then
    try main () with ex -> begin
        let msg = match ex with
          | Failure msg -> msg
          | _ -> Printexc.to_string ex
        in
        Printf.eprintf "Failure: %s\n%!" msg ;
        exit 1
      end
