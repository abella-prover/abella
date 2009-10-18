(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
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
open Typing
open Printf

type uclause = uterm * uterm list
type uclauses = uclause list

type clause = term * term list
type clauses = clause list

type def_type = Inductive | CoInductive

type udef = umetaterm * umetaterm
type udefs = udef list
type def = metaterm * metaterm
type defs = def list
type defs_table = (string, def_type * string list * def list) Hashtbl.t

type id = string

type set_value =
  | Str of string
  | Int of int

type top_command =
  | Theorem of id * umetaterm
  | Define of (id * ty) list * udefs
  | CoDefine of (id * ty) list * udefs
  | TopSet of string * set_value
  | Import of string
  | Specification of string
  | Query of umetaterm
  | Kind of id list
  | Type of id list * ty

type compiled =
  | CTheorem of id * metaterm
  | CDefine of (id * ty) list * defs
  | CCoDefine of (id * ty) list * defs
  | CImport of string
  | CKind of id list
  | CType of id list * ty

type command =
  | Induction of int list
  | CoInduction
  | Apply of id * id list * (id * uterm) list
  | Backchain of id * (id * uterm) list
  | Cut of id * id
  | Inst of id * id * uterm
  | Case of id * bool
  | Assert of umetaterm
  | Exists of uterm
  | Clear of id list
  | Abbrev of id * string
  | Unabbrev of id list
  | Monotone of id * uterm
  | Permute of id list * id option
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
  | Set of string * set_value

let udef_to_string (head, body) =
  if body = UTrue then
    umetaterm_to_string head
  else
    sprintf "%s := %s" (umetaterm_to_string head)
      (umetaterm_to_formatted_string body)

let udefs_to_string udefs =
  String.concat ";\n" (List.map udef_to_string udefs)

let def_type_to_string dtype =
  match dtype with
    | Inductive -> "inductive"
    | CoInductive -> "coinductive"

let set_value_to_string v =
  match v with
    | Str s -> s
    | Int d -> string_of_int d

let id_list_to_string ids =
  String.concat ", " ids

let idtys_to_string idtys =
  String.concat ",\t\n"
    (List.map (fun (id, ty) -> id ^ " : " ^ (ty_to_string ty)) idtys)

let top_command_to_string tc =
  match tc with
    | Theorem(name, body) ->
        sprintf "Theorem %s : \n%s" name (umetaterm_to_formatted_string body)
    | Define(idtys, udefs) ->
        sprintf "Define %s by \n%s"
          (idtys_to_string idtys) (udefs_to_string udefs) ;
    | CoDefine(idtys, udefs) ->
        sprintf "CoDefine %s by \n%s"
          (idtys_to_string idtys) (udefs_to_string udefs) ;
    | TopSet(k, v) ->
        sprintf "Set %s %s" k (set_value_to_string v)
    | Import filename ->
        sprintf "Import \"%s\"" filename
    | Specification filename ->
        sprintf "Specification \"%s\"" filename
    | Query q ->
        sprintf "Query %s" (umetaterm_to_formatted_string q)
    | Kind ids ->
        sprintf "Kind %s type" (id_list_to_string ids)
    | Type(ids, ty) ->
        sprintf "Type %s %s" (id_list_to_string ids) (ty_to_string ty)

let withs_to_string ws =
  String.concat ", "
    (List.map (fun (x,t) -> x ^ " = " ^ (uterm_to_string t)) ws)

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
    | Backchain(h, []) ->
        sprintf "backchain %s" h
    | Backchain(h, ws) ->
        sprintf "backchain %s with %s" h (withs_to_string ws)
    | Cut(h1, h2) ->
        sprintf "cut %s with %s" h1 h2
    | Inst(h, n, t) ->
        sprintf "inst %s with %s = %s" h n (uterm_to_string t)
    | Case(h, k) ->
        sprintf "case %s" h ^ if k then " (keep)" else ""
    | Assert t ->
        sprintf "assert %s" (umetaterm_to_formatted_string t)
    | Exists t ->
        sprintf "exists %s" (uterm_to_string t)
    | Clear hs ->
        sprintf "clear %s" (String.concat " " hs)
    | Abbrev(h, s) ->
        sprintf "abbrev %s \"%s\"" h s
    | Unabbrev hs ->
        sprintf "unabbrev %s" (String.concat " " hs)
    | Monotone(h, t) ->
        sprintf "monotone %s with %s" h (uterm_to_string t)
    | Permute(ids, t) ->
        sprintf "permute (%s)%s"
          (String.concat " " ids)
          (match t with None -> "" | Some h -> " " ^ h)
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
    | Set(k, v) -> sprintf "Set %s %s" k (set_value_to_string v)
