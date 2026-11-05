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

(* Build web/examples/bundle.json from a curated example manifest. *)

open Abella_lib
open Extensions

type example = {
  id : string ;
  group : string ;
  name : string ;
  entry : string ;
}

let read_file path =
  let ch = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ch) begin fun () ->
    really_input_string ch (in_channel_length ch)
  end

let string_field name fields =
  match List.assoc_opt name fields with
  | Some (`String s) -> s
  | _ -> failwithf "Missing string field %S" name

let parse_example = function
  | `Assoc fields ->
      { id = string_field "id" fields ;
        group = string_field "group" fields ;
        name = string_field "name" fields ;
        entry = string_field "entry" fields }
  | _ -> failwithf "Example entries must be objects"

let read_manifest path =
  match Json.from_file path with
  | `Assoc fields -> begin
      match List.assoc_opt "examples" fields with
      | Some (`List examples) -> List.map parse_example examples
      | _ -> failwithf "Manifest must have an \"examples\" list"
    end
  | _ -> failwithf "Manifest must be a JSON object"

let is_source path =
  List.exists (Filename.check_suffix path)
    [".thm" ; ".thmod" ; ".sig" ; ".mod"]

let files_in_dir entry predicate =
  let dir = Filename.dirname entry in
  if Sys.file_exists dir && Sys.is_directory dir then
    Sys.readdir dir |>
    Array.to_list |>
    List.filter predicate |>
    List.map (Filename.concat dir)
  else
    []

let source_files_for entry =
  files_in_dir entry is_source

(* Transitive .thm/.thmod files and spec files for one root.  A source
   entry pulls in its dependency closure; a text entry pulls in every
   source file beside it. *)
let dependencies entry =
  let seen = Hashtbl.create 19 in
  let thms = ref [] in
  let thmods = ref [] in
  let specs = ref [] in
  let rec visit_thm base =
    let key = "thm:" ^ base in
    if not (Hashtbl.mem seen key) then begin
      Hashtbl.add seen key () ;
      let deps = Depend.file_dependencies `thm base in
      thms := (base ^ ".thm") :: !thms ;
      specs := deps.Depend.dep_specs @ !specs ;
      List.iter visit_thm deps.Depend.dep_thms ;
      List.iter visit_thmod deps.Depend.dep_thmods
    end
  and visit_thmod base =
    let key = "thmod:" ^ base in
    if not (Hashtbl.mem seen key) then begin
      Hashtbl.add seen key () ;
      let deps = Depend.file_dependencies `thmod base in
      thmods := (base ^ ".thmod") :: !thmods ;
      specs := deps.Depend.dep_specs @ !specs ;
      List.iter visit_thm deps.Depend.dep_thms ;
      List.iter visit_thmod deps.Depend.dep_thmods
    end
  in
  let visit_source path =
    if Filename.check_suffix path ".thm" then
      visit_thm (Filename.chop_suffix path ".thm")
    else if Filename.check_suffix path ".thmod" then
      visit_thmod (Filename.chop_suffix path ".thmod")
    else if Filename.check_suffix path ".sig" ||
            Filename.check_suffix path ".mod" then
      specs := path :: !specs
  in
  List.iter visit_source begin
    if Filename.check_suffix entry ".thm" then [entry]
    else source_files_for entry
  end ;
  (List.rev !thms, List.rev !thmods, List.unique !specs)

let is_small_text path =
  Filename.check_suffix path ".md" || Filename.check_suffix path ".txt"

let text_files_for entry =
  files_in_dir entry is_small_text |>
  List.filter (fun path ->
      (Unix.stat path).Unix.st_size <= 64 * 1024)

let build_example (files : (string, string) Hashtbl.t) example =
  let thms, thmods, specs = dependencies example.entry in
  let paths =
    List.unique (thms @ thmods @ specs @ text_files_for example.entry) |>
    List.sort String.compare
  in
  List.iter (fun path -> Hashtbl.replace files path (read_file path)) paths ;
  let base =
    if Filename.check_suffix example.entry ".thm" then
      Some (Filename.chop_suffix example.entry ".thm")
    else
      None
  in
  let suffix_path suffix =
    match base with
    | Some base when List.mem (base ^ suffix) specs -> `String (base ^ suffix)
    | _ -> `Null
  in
  `Assoc [
    "id", `String example.id ;
    "group", `String example.group ;
    "name", `String example.name ;
    "entry", `String example.entry ;
    "sig", suffix_path ".sig" ;
    "mod", suffix_path ".mod" ;
    "files", `List (List.map (fun path -> `String path) paths) ;
  ]

let main manifest_path output_path =
  let examples = read_manifest manifest_path in
  let files = Hashtbl.create 97 in
  let entries = List.map (build_example files) examples in
  let files =
    Hashtbl.fold (fun path contents acc -> (path, `String contents) :: acc)
      files [] |>
    List.sort (fun (a, _) (b, _) -> String.compare a b)
  in
  let bundle = `Assoc [
    "version", `Int 1 ;
    "examples", `List entries ;
    "files", `Assoc files ;
  ] in
  let out = open_out_bin output_path in
  Fun.protect ~finally:(fun () -> close_out out) begin fun () ->
    output_string out (Json.to_string bundle)
  end

let () =
  let open Cmdliner in
  let manifest =
    let doc = "Curated example manifest (JSON)." in
    Arg.(required @@ opt (some string) None @@
         info ["m" ; "manifest"] ~doc ~docv:"FILE")
  in
  let output =
    let doc = "Output bundle." in
    Arg.(required @@ opt (some string) None @@
         info ["o" ; "output"] ~doc ~docv:"FILE")
  in
  let cmd =
    let doc = "Generate the Abella Web example bundle." in
    Cmd.v (Cmd.info "abella_bundle" ~doc)
      Term.(const (fun m o -> main m o) $ manifest $ output)
  in
  exit (Cmd.eval cmd)
