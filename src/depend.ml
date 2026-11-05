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

open Accumulate
open Extensions

module type LP = sig
  val extension : string
  val immediate_depends : string -> string list
end

module LPSig : LP = struct
  let extension = ".sig"
  let immediate_depends filename =
    let Sig { accum_sig ; _ } = read_lpsig filename in
    List.map (fun { el ; _ } -> el) accum_sig
end

module LPMod : LP = struct
  let extension = ".mod"
  let immediate_depends filename =
    let Mod { accum ; _ } = read_lpmod filename in
    List.map (fun { el ; _ } -> el) accum
end

let lp_depend_cache : (string, string list option) Hashtbl.t = Hashtbl.create 19

let rec lp_dependencies (module Lp : LP) lpfile =
  let filename = lpfile ^ Lp.extension in
  match Hashtbl.find lp_depend_cache filename with
  | None ->
      failwithf "Cyclic dependency in %S" filename
  | Some deps -> deps
  | exception Not_found ->
      Hashtbl.add lp_depend_cache filename None ;
      let imms = Lp.immediate_depends lpfile in
      let deps = filename :: List.flatten_map (lp_dependencies (module Lp : LP)) imms in
      Hashtbl.replace lp_depend_cache filename (Some deps) ;
      deps

type file_kind = [`thm | `thmod]

type dependencies = {
  dep_specs : string list ;
  dep_thms : string list ;
  dep_thmods : string list ;
}

let file_dependencies kind filename =
  let extension = match kind with `thm -> ".thm" | `thmod -> ".thmod" in
  let lexbuf = lexbuf_from_file (filename ^ extension) in
  let rec spin ~specs ~thms ~thmods =
    match (Parser.any_command_start Lexer.token lexbuf).el with
    | ATopCommand (Specification (s, _)) ->
        spin ~thms ~thmods
          ~specs:(Filepath.normalize ~wrt:filename s :: specs)
    | ATopCommand (Import (i, _, _)) ->
        spin ~specs ~thmods
          ~thms:(Filepath.normalize ~wrt:filename i :: thms)
    | ATopCommand (ImportModule mi) ->
        let thmods =
          match mi.mi_source with
          | QuoteSource (s, _) ->
              Filepath.normalize ~wrt:filename s :: thmods
          | NameSource _ -> thmods
        in
        spin ~specs ~thms ~thmods
    | ACommon (ShowModule (QuoteSource (s, _))) ->
        spin ~specs ~thms
          ~thmods:(Filepath.normalize ~wrt:filename s :: thmods)
    | ACommon (ShowModule _) ->
        spin ~specs ~thms ~thmods
    | ACommon (Set ("load_path", QStr lp)) ->
        Filepath.set_load_path ~wrt:filename lp ;
        spin ~specs ~thms ~thmods
    | _ -> spin ~specs ~thms ~thmods
    | exception End_of_file ->
        { dep_specs = List.rev specs |> List.unique ;
          dep_thms = List.rev thms |> List.unique ;
          dep_thmods = List.rev thmods |> List.unique ;
        }
    | exception Parsing.Parse_error ->
        failwithf "Syntax error%s" (position lexbuf)
  in
  let deps = spin ~specs:[] ~thms:[] ~thmods:[] in
  let sigfiles =
    List.flatten_map (lp_dependencies (module LPSig : LP)) deps.dep_specs
  in
  let modfiles =
    List.flatten_map (lp_dependencies (module LPMod : LP)) deps.dep_specs
  in
  { deps with dep_specs = List.unique (sigfiles @ modfiles) }

let thm_dependencies filename =
  let deps = file_dependencies `thm filename in
  (deps.dep_specs, deps.dep_thms)
