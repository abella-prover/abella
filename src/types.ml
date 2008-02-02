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

type meta_clause = metaterm * metaterm list
type meta_clauses = meta_clause list

type id = string

type top_command =
  | Theorem of id * metaterm
  | Axiom of id * metaterm
  | Def of meta_clause

type command =
  | Induction of int
  | Apply of id * id list
  | Cut of id * id
  | Inst of id * id * term
  | Case of id * bool
  | Assert of metaterm
  | Exists of term
  | Clear of id list
  | Search
  | Split
  | SplitStar
  | Intros
  | Unfold
  | Skip
  | Abort
  | Undo

let meta_clause_to_string (head, body) =
  if body = [] then
    metaterm_to_string head
  else
    sprintf "%s :- %s"
      (metaterm_to_string head)
      (String.concat ", " (List.map metaterm_to_string body))

let top_command_to_string tc =
  match tc with
    | Theorem(name, body) ->
        sprintf "Theorem %s : \n%s" name (metaterm_to_formatted_string body)
    | Axiom(name, body) ->
        sprintf "Axiom %s : %s" name (metaterm_to_formatted_string body)
    | Def clause ->
        sprintf "Def %s" (meta_clause_to_string clause)

let command_to_string c =
  match c with
    | Induction i ->
        sprintf "induction on %d" i
    | Apply(h, hs) ->
        sprintf "apply %s to %s" h (String.concat " " hs)
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
    | Search -> "search"
    | Split -> "split"
    | SplitStar -> "split*"
    | Unfold -> "unfold"
    | Intros -> "intros"
    | Skip -> "skip"
    | Abort -> "abort"
    | Undo -> "undo"
      
