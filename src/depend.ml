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
    List.map (fun Typing.{ el ; _ } -> el) accum_sig
end

module LPMod : LP = struct
  let extension = ".mod"
  let immediate_depends filename =
    let Mod { accum ; _ } = read_lpmod filename in
    List.map (fun Typing.{ el ; _ } -> el) accum
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
      let deps = filename :: List.flatten_map (lp_dependencies (module Lp)) imms in
      Hashtbl.replace lp_depend_cache filename (Some deps) ;
      deps

let thm_dependencies filename =
  let lexbuf = lexbuf_from_file (filename ^ ".thm") in
  let rec spin ~specs ~imports =
    match (Parser.any_command_start Lexer.token lexbuf).el with
    | ATopCommand (Specification (s, _)) ->
        spin ~imports
          ~specs:(Filepath.normalize ~wrt:filename s :: specs)
    | ATopCommand (Import (i, _, _)) ->
        spin ~specs
          ~imports:(Filepath.normalize ~wrt:filename i :: imports)
    | ACommon (Set ("load_path", QStr lp)) ->
        Filepath.set_load_path ~wrt:filename lp ;
        spin ~specs ~imports
    | _ -> spin ~specs ~imports
    | exception End_of_file -> (List.rev specs |> List.unique,
                                List.rev imports |> List.unique)
    | exception Parsing.Parse_error ->
        failwithf "Syntax error%s" (position lexbuf)
  in
  let (specs, imports) = spin ~specs:[] ~imports:[] in
  let sigfiles = List.flatten_map (lp_dependencies (module LPSig)) specs in
  let modfiles = List.flatten_map (lp_dependencies (module LPMod)) specs in
  (sigfiles @ modfiles, imports)
