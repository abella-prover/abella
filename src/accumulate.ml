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

open Abella_types
open Typing
open Extensions
open Format

module H = Hashtbl

let mod_cache = H.create 10
let sig_cache = H.create 10

let clear_specification_cache () =
  H.clear mod_cache ;
  H.clear sig_cache

let lexbuf_from_file filename =
  let lexbuf = Lexing.from_channel (open_in filename) in
    lexbuf.Lexing.lex_curr_p <- {
      lexbuf.Lexing.lex_curr_p with
        Lexing.pos_fname = filename } ;
    lexbuf

let position lexbuf =
  let curr = lexbuf.Lexing.lex_curr_p in
  let file = curr.Lexing.pos_fname in
  let line = curr.Lexing.pos_lnum in
  let char = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    if file = "" then
      "" (* lexbuf information is rarely accurate at the toplevel *)
    else
      sprintf ": file %s, line %d, character %d" file line char

let read_lp ext parser name =
  let lexbuf = lexbuf_from_file (name ^ ext) in
    try
      parser Lexer.token lexbuf
    with
      | Parsing.Parse_error ->
          eprintf "Syntax error%s.\n%!" (position lexbuf) ;
          failwith "Failed while reading specification"

let read_lpsig = read_lp ".sig" Parser.lpsig
let read_lpmod = read_lp ".mod" Parser.lpmod

let merge_signs signs =
  let (ktables, ctables) = List.split signs in
  let ktable = List.flatten ktables in
    List.fold_left add_poly_consts (ktable, []) ctables

let add_decl sign = function
  | SKind(tynames, knd) -> add_types sign tynames knd
  | SType(ids, ty) ->
      check_spec_logic_type ty ;
      add_consts sign (List.map (fun id -> (id, ty)) ids)

let rec get_sign_accum_sigs filename =
  try match H.find sig_cache filename with
    | None -> failwith ("Cyclic dependency in signature " ^ filename)
    | Some (sign, accum_sigs) -> (sign, accum_sigs)
  with
    | Not_found ->
        H.add sig_cache filename None ;
        let Sig(name, accums, decls) = read_lpsig filename in
          if name <> Filename.basename filename then
            failwithf "Expected 'sig %s.' but found 'sig %s.'"
              (Filename.basename filename) name ;
          let accum_signs = List.map get_sign accums in
          let sign = merge_signs (pervasive_sign :: accum_signs) in
          let sign = List.fold_left add_decl sign decls in
            H.replace sig_cache filename (Some(sign, accums)) ;
            (sign, accums)
and get_sign filename = fst (get_sign_accum_sigs filename)

let merge_named_clauses ncs =
  let cmp (x, _) (y, _) = (x=y) in
    List.unique ~cmp ncs

let ensure_no_redefine_keywords name uclauses =
  List.iter
    (fun (_, head, _) ->
       let id = uterm_head_name head in
         if id = "pi" || id = "=>" || id = "&" then
           failwithf "Module %s attempts to re-define keyword %s"
             name id)
    uclauses

let rec get_named_clauses ~sr filename =
  try match H.find mod_cache filename with
    | None -> failwith ("Cyclic dependency in module " ^ filename)
    | Some nclauses -> nclauses
  with
    | Not_found ->
        H.add mod_cache filename None ;
        let Mod(name, accumulate, uclauses) = read_lpmod filename in
          if name <> Filename.basename filename then
            failwithf "Expected 'module %s.' but found 'module %s.'"
              (Filename.basename filename) name ;
          ensure_no_redefine_keywords name uclauses ;
          let (sign, accum_sigs) = get_sign_accum_sigs filename in
          let non_accum = List.minus accumulate accum_sigs in
          let () = if non_accum <> [] then
            failwithf "Signature %s must accum_sig %s."
              filename (String.concat ", " non_accum)
          in
          let accum_clauses = List.flatten_map (get_named_clauses ~sr) accumulate in
          let nclauses = (merge_named_clauses accum_clauses) @
            [filename, List.map (type_uclause ~sr ~sign) uclauses]
          in
            H.replace mod_cache filename (Some nclauses) ;
            nclauses

let get_clauses ~sr filename =
  List.flatten_map snd (get_named_clauses ~sr filename)
