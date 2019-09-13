(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2018 Inria (Institut National de Recherche            *)
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

open Metaterm
open Term
open Typing
open Printf
open Extensions

type uclause = string option * uterm * uterm list
type clause = string list * term

type flavor = Inductive | CoInductive

type udef_clause = umetaterm * umetaterm
type def_clause = {
  head : metaterm ;
  body : metaterm ;
}
type def = {
  flavor   : flavor ;
  typarams : string list ;
  mutual   : ty Itab.t ;
  clauses  : def_clause list ;
}
type defs_table = (string, def) Hashtbl.t

type id = string

exception Reported_parse_error

type set_value =
  | Str of string
  | Int of int
  | QStr of string

type clearable =
  | Keep of id * ty list
  | Remove of id * ty list

type common_command =
  | Back | Reset
  | Set of string * set_value
  | Show of string
  | Quit

type top_command =
  | Theorem of id * string list * umetaterm
  | Define of flavor * tyctx * udef_clause list
  | Import of string * (string * string) list
  | Specification of string
  | Query of umetaterm
  | Kind of id list * knd
  | Type of id list * ty
  | Close of aty list
  | SSplit of id * id list
  | TopCommon of common_command

type compiled =
  | CTheorem of id * string list * metaterm
  | CDefine of flavor * string list * tyctx * def_clause list
  | CImport of string * (string * string) list
  | CKind of id list * knd
  | CType of id list * ty
  | CClose of (aty * aty list) list

type witness =
  | WTrue
  | WHyp of id
  | WLeft of witness
  | WRight of witness
  | WSplit of witness * witness
  | WForall of id list * witness
  | WIntros of id list * witness
  | WExists of (id * term) list * witness
  | WReflexive
  | WUnfold of id * int * witness list
  | WMagic

let witness_to_string =
  let bind_to_string (id, t) =
    id ^ " = " ^ term_to_string t
  in

  let rec aux = function
    | WTrue -> "true"
    | WHyp id -> "apply " ^ id
    | WLeft w -> "left " ^ aux w
    | WRight w -> "right " ^ aux w
    | WSplit(w1,w2) -> "split(" ^ aux w1 ^ ", " ^ aux w2 ^ ")"
    | WForall(ids,w) ->
        "forall[" ^ (String.concat ", " ids) ^ "] " ^ aux w
    | WIntros(ids,w) ->
        "intros[" ^ (String.concat ", " ids) ^ "] " ^ aux w
    | WExists(binds,w) ->
        "exists[" ^ (String.concat ", " (List.map bind_to_string binds)) ^
        "] " ^ aux w
    | WReflexive -> "="
    | WUnfold(id,n,[]) ->
        Printf.sprintf "unfold(%s, %d)" id n
    | WUnfold(id,n,ws) ->
        let ws = List.map aux ws |> String.concat ", " in
        Printf.sprintf "unfold(%s, %d, %s)" id n ws
    | WMagic -> "*"
  in
  aux

type depth_bound = int

type ewitness =
  | ETerm of uterm
  | ESub of id * uterm

type clear_mode =
  | Clear_delete
  | Clear_extro

type hhint = id option

type command =
  | Induction of int list * hhint
  | CoInduction of id option
  | Apply of depth_bound option * clearable * clearable list * (id * uterm) list * hhint * bool (* false: apply; true: applys *)
  | Backchain of depth_bound option * clearable * (id * uterm) list
  | CutFrom of clearable * clearable * uterm * hhint
  | Cut of clearable * clearable * hhint
  | SearchCut of clearable * hhint
  | Inst of clearable * (id * uterm) list * hhint
  | Case of clearable * hhint
  | Assert of umetaterm * int option * hhint
  | Monotone of clearable * uterm * hhint
  | Exists of [`EXISTS | `WITNESS] * ewitness list
  | Clear of clear_mode * id list
  | Abbrev of id list * string
  | Unabbrev of id list
  | Rename of id * id
  | Permute of id list * id option
  | Search of [`nobounds | `depth of depth_bound | `witness of witness]
  | Async_steps
  | Split
  | SplitStar
  | Left
  | Right
  | Intros of id list
  | Unfold of clause_selector * solution_selector
  | Skip
  | Abort
  | Undo
  | Common of common_command

and clause_selector =
  | Select_any
  | Select_num of int
  | Select_named of string

and solution_selector =
  | Solution_first
  | Solution_all

type any_command =
  | ATopCommand of top_command
  | ACommand of command
  | ACommon of common_command

type sig_decl =
  | SKind of id list * knd
  | SType of id list * ty

type lpsig =
  | Sig of string * string list * sig_decl list

type lpmod =
  | Mod of string * string list * uclause list

let udef_to_string (head, body) =
  if body = UTrue then
    umetaterm_to_string head
  else
    sprintf "%s := %s" (umetaterm_to_string head)
      (umetaterm_to_formatted_string body)

let udef_clauses_to_string cls =
  String.concat ";\n" (List.map udef_to_string cls)

let flavor_to_string dtype =
  match dtype with
    | Inductive -> "inductive"
    | CoInductive -> "coinductive"

let set_value_to_string v =
  match v with
    | Str s -> s
    | Int d -> string_of_int d
    | QStr s -> sprintf "%S" s

let id_list_to_string ids =
  String.concat ", " ids

let idtys_to_string idtys =
  String.concat ",\t\n"
    (List.map (fun (id, ty) -> id ^ " : " ^ (ty_to_string ty)) idtys)

let inst_to_string tys =
  match tys with
  | [] -> ""
  | _ -> "[" ^ (List.map ty_to_string tys |> String.concat ",") ^ "]"

let clearable_to_string cl =
  match cl with
  | Keep (h, tys) -> h ^ inst_to_string tys
  | Remove (h, tys) -> "*" ^ h ^ inst_to_string tys

let common_command_to_string cc =
  match cc with
  | Back ->
      sprintf "#<back>"
  | Reset ->
      sprintf "#<reset>"
  | Set(k, v) ->
      sprintf "Set %s %s" k (set_value_to_string v)
  | Show nm ->
      sprintf "Show %s" nm
  | Quit ->
      sprintf "Quit"

let gen_to_string tys =
  match tys with
  | [] -> ""
  | _ -> " [" ^ String.concat "," tys ^ "]"

let aty_list_to_string atys = 
  String.concat "," (List.map aty_to_string atys)

let top_command_to_string tc =
  match tc with
    | Theorem(name, tys, body) ->
        sprintf "Theorem %s%s : \n%s" name (gen_to_string tys)
          (umetaterm_to_formatted_string body)
    | Define(flavor, idtys, cls) ->
        sprintf "%s %s by \n%s"
          (match flavor with Inductive -> "Define" | _ -> "CoDefine")
          (idtys_to_string idtys) (udef_clauses_to_string cls) ;
    | Import (filename, withs) ->
        sprintf "Import \"%s\"%s%s" filename
          (if withs = [] then "" else " with ")
          (withs |>
           List.map (fun (a, b) -> a ^ " := " ^ b) |>
           String.concat ", ")
    | Specification filename ->
        sprintf "Specification \"%s\"" filename
    | Query q ->
        sprintf "Query %s" (umetaterm_to_formatted_string q)
    | Kind (ids, knd) ->
        sprintf "Kind %s %s" (id_list_to_string ids) (knd_to_string knd)
    | Type(ids, ty) ->
        sprintf "Type %s %s" (id_list_to_string ids) (ty_to_string ty)
    | Close atys ->
        sprintf "Close %s" (aty_list_to_string atys)
    | SSplit(id, ids) ->
        if ids <> [] then
          sprintf "Split %s as %s" id (id_list_to_string ids)
        else
          sprintf "Split %s" id
    | TopCommon(cc) ->
        common_command_to_string cc

let withs_to_string ws =
  String.concat ", "
    (List.map (fun (x,t) -> x ^ " = " ^ (uterm_to_string t)) ws)

let hn_to_string = function
  | None -> ""
  | Some hn -> sprintf "%s : " hn

let clearables_to_string cls =
  List.map clearable_to_string cls |> String.concat " "

let dbound_to_string = function
  | None -> ""
  | Some n -> " " ^ string_of_int n

let ewitness_to_string = function
  | ETerm t -> uterm_to_string t
  | ESub (x, t) -> x ^ " = " ^ uterm_to_string t

let command_to_string c =
  match c with
    | Induction(is, hn) ->
        sprintf "%sinduction on %s" (hn_to_string hn)
          (String.concat " " (List.map string_of_int is))
    | CoInduction None -> "coinduction"
    | CoInduction (Some hn) -> "coinduction " ^ hn
    | Apply(dbound, h, hs, ws, hn, applys) -> begin
        let buf = Buffer.create 10 in
        Buffer.add_string buf (hn_to_string hn) ;
        Buffer.add_string buf "apply" ;
        if applys then Buffer.add_string buf "s" ;
        Buffer.add_string buf (dbound_to_string dbound) ;
        Buffer.add_string buf (" " ^ clearable_to_string h) ;
        if hs <> [] then
          (Buffer.add_string buf " to " ;
           Buffer.add_string buf (clearables_to_string hs)) ;
        if ws <> [] then
          (Buffer.add_string buf " with " ;
           Buffer.add_string buf (withs_to_string ws)) ;
        Buffer.contents buf
      end
    | Backchain(dbound, h, []) ->
        sprintf "backchain%s %s"
          (dbound_to_string dbound)
          (clearable_to_string h)
    | Backchain(dbound, h, ws) ->
        sprintf "backchain%s %s with %s"
          (dbound_to_string dbound)
          (clearable_to_string h)
          (withs_to_string ws)
    | Cut(h1, h2, hn) ->
        sprintf "%scut %s with %s"
          (hn_to_string hn)
          (clearable_to_string h1)
          (clearable_to_string h2)
    | CutFrom(h, arg, t, hn) ->
        sprintf "%scut %s from %s with %s"
          (hn_to_string hn) (uterm_to_string t)
          (clearable_to_string h)
          (clearable_to_string arg)
    | SearchCut(h, hn) ->
        sprintf "%s cut %s" (hn_to_string hn)
          (clearable_to_string h)
    | Inst(h, ws, hn) ->
        sprintf "%s inst %s with %s" (hn_to_string hn)
          (clearable_to_string h)
          (withs_to_string ws)
    | Case(Keep (h, _), hn) ->
        sprintf "%scase %s (keep)" (hn_to_string hn) h
    | Case(Remove (h, _), hn) ->
        sprintf "%scase %s" (hn_to_string hn) h
    | Assert(t, dp, hn) ->
        sprintf "%sassert %s%s"
          (hn_to_string hn)
          (match dp with
           | Some dp -> string_of_int dp ^ " "
           | None -> "")
          (umetaterm_to_formatted_string t)
    | Monotone(h, t, hn) ->
        sprintf "%smonotone %s with %s"
          (hn_to_string hn)
          (clearable_to_string h)
          (uterm_to_string t)
    | Exists (how, ews) ->
        let hows = match how with
          | `EXISTS -> "exists"
          | `WITNESS -> "witness"
        in
        sprintf "%s %s" hows
          (List.map ewitness_to_string ews |> String.concat ", ")
    | Clear (cm, hs) ->
        sprintf "clear %s%s"
          (match cm with
           | Clear_delete -> ""
           | Clear_extro -> " -> ")
          (String.concat " " hs)
    | Abbrev(hs, s) ->
        sprintf "abbrev %s \"%s\"" (String.concat " " hs) s
    | Unabbrev hs ->
        sprintf "unabbrev %s" (String.concat " " hs)
    | Rename(hfrom, hto) ->
        sprintf "rename %s to %s" hfrom hto
    | Permute(ids, t) ->
        sprintf "permute (%s)%s"
          (String.concat " " ids)
          (match t with None -> "" | Some h -> " " ^ h)
    | Search(`nobounds) -> "search"
    | Search(`depth d) -> sprintf "search %d" d
    | Search(`witness w) -> sprintf "search with %s" (witness_to_string w)
    | Async_steps -> "async"
    | Split -> "split"
    | SplitStar -> "split*"
    | Left -> "left"
    | Right -> "right"
    | Unfold (clause_sel, sol_sel) ->
        sprintf "unfold%s%s"
          (match clause_sel with
           | Select_any -> ""
           | Select_num n -> " " ^ string_of_int n
           | Select_named n -> " " ^ n)
          (match sol_sel with
           | Solution_first -> ""
           | Solution_all -> " (all)")
    | Intros [] -> "intros"
    | Intros ids -> sprintf "intros %s" (String.concat " " ids)
    | Skip -> "skip"
    | Abort -> "abort"
    | Undo -> "undo"
    | Common(cc) -> common_command_to_string cc
