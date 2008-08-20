(****************************************************************************)
(* Copyright (C) 2007-2008 Gacek                                            *)
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

open Metaterm
open Term
open Printf

type clause = term * term list
type clauses = clause list

type def_type = Inductive | CoInductive
    
type def = metaterm * metaterm
type defs = (string * int, def_type * def list) Hashtbl.t

type id = string

type top_command =
  | Theorem of id * metaterm
  | Define of def
  | CoDefine of def

type command =
  | Induction of int list
  | CoInduction
  | Apply of id * id list * (id * term) list
  | Cut of id * id
  | Inst of id * id * term
  | Case of id * bool
  | Assert of metaterm
  | Exists of term
  | Clear of id list
  | Search of int option
  | Split
  | SplitStar
  | Left
  | Right
  | Intros
  | Unfold
  | Skip
  | Abort
  | Undo

let def_to_string (head, body) =
  if body = True then
    metaterm_to_string head
  else
    sprintf "%s := %s" (metaterm_to_string head)
      (metaterm_to_formatted_string body)

let def_type_to_string dtype =
  match dtype with
    | Inductive -> "inductive"
    | CoInductive -> "coinductive"

let top_command_to_string tc =
  match tc with
    | Theorem(name, body) ->
        sprintf "Theorem %s : \n%s" name (metaterm_to_formatted_string body)
    | Define def ->
        sprintf "Define %s" (def_to_string def)
    | CoDefine def ->
        sprintf "CoDefine %s" (def_to_string def)

let withs_to_string ws =
  String.concat ", "
    (List.map (fun (x,t) -> x ^ " = " ^ (term_to_string t)) ws)

let command_to_string c =
  match c with
    | Induction is ->
        sprintf "induction on %s"
          (String.concat " " (List.map string_of_int is))
    | CoInduction -> "coinduction"
    | Apply(h, [], []) ->
        sprintf "apply %s" h
    | Apply(h, hs, []) ->
        sprintf "apply %s to %s" h (String.concat " " hs)
    | Apply(h, [], ws) ->
        sprintf "apply %s with %s" h (withs_to_string ws)
    | Apply(h, hs, ws) ->
        sprintf "apply %s to %s with %s" h (String.concat " " hs)
          (withs_to_string ws)
    | Cut(h1, h2) ->
        sprintf "cut %s with %s" h1 h2
    | Inst(h, n, t) ->
        sprintf "inst %s with %s = %s" h n (term_to_string t)
    | Case(h, k) ->
        sprintf "case %s" h ^ if k then " (keep)" else ""
    | Assert t ->
        sprintf "assert %s" (metaterm_to_formatted_string t)
    | Exists t ->
        sprintf "exists %s" (term_to_string t)
    | Clear hs ->
        sprintf "clear %s" (String.concat " " hs)
    | Search(None) -> "search"
    | Search(Some d) -> sprintf "search %d" d
    | Split -> "split"
    | SplitStar -> "split*"
    | Left -> "left"
    | Right -> "right"
    | Unfold -> "unfold"
    | Intros -> "intros"
    | Skip -> "skip"
    | Abort -> "abort"
    | Undo -> "undo"
      
