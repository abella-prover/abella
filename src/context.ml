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

open Term
open Extensions

(* Basic operations *)

type elt = term
type t = elt list

let empty : t = []

let size ctx = List.length ctx

let mem elt ctx =
  if has_logic_head elt then
    (* The tail variable - do not unify yet *)
    List.mem ~cmp:eq elt ctx
  else
    List.mem ~cmp:Unify.try_right_unify elt ctx

let remove elt ctx = List.remove ~cmp:Unify.try_right_unify elt ctx

let rec xor ctx1 ctx2 =
  match ctx1 with
    | [] -> ([], ctx2)
    | head::tail ->
        if mem head ctx2
        then xor tail (remove head ctx2)
        else let ctx1', ctx2' = xor tail ctx2 in
          (head::ctx1', ctx2')

let add elt ctx = ctx @ [elt]

let is_empty ctx = ctx = []

let element_to_string elt =
  term_to_string elt

let context_to_string ctx =
  let rec aux lst =
    match lst with
      | [] -> ""
      | [last] -> element_to_string last
      | head::tail -> (element_to_string head) ^ ", " ^ (aux tail)
  in
    aux ctx

let cons = const "::" (tyarrow [oty; olistty] olistty)
let nil = const "nil" olistty
let imp = const "=>" (tyarrow [oty; oty] oty)
let amp = const "&" (tyarrow [oty; oty] oty)

let is_nil t =
  Term.is_head_name "nil" t

let is_cons t =
  Term.is_head_name "::" t

let extract_cons t =
  match observe (hnorm t) with
    | App(_, [a; b]) -> (a, b)
    | _ -> assert false

let normalize ctx =
  let remove_dups ctx = List.unique ~cmp:eq ctx in
  let rec remove_cons ctx =
    match ctx with
      | [] -> []
      | head::tail when is_cons head ->
          let a, b = extract_cons head in
            remove_cons (b::a::tail)
      | head::tail when is_nil head ->
          remove_cons tail
      | head::tail -> head::(remove_cons tail)
  in
    remove_dups (remove_cons ctx)

let subcontext ctx1 ctx2 =
  let ctx1 = normalize ctx1 in
  let ctx2 = normalize ctx2 in
    List.for_all (fun elt -> mem elt ctx2) ctx1

let equiv ctx1 ctx2 = subcontext ctx1 ctx2 && subcontext ctx2 ctx1

(* Be sure to move any tail variables to the front *)
let union ctx1 ctx2 =
  match ctx2 with
    | [] -> ctx1
    | c::cs ->
        if tc [] c = olistty then
          c :: ctx1 @ cs
        else
          ctx1 @ ctx2

let union_list ctx_list =
  List.fold_left union empty ctx_list

let exists f ctx = List.exists f ctx

let map f ctx = List.map f ctx

let iter f ctx = List.iter f ctx

let rec group pair_list =
  match pair_list with
    | [] -> []
    | (a, _b)::_ ->
        let pairings = List.assoc_all ~cmp:eq a pair_list in
        let pair_list' = List.remove_all_assoc ~cmp:eq a pair_list in
          (a, pairings)::(group pair_list')

let context_to_list ctx = ctx

let context_to_term ctx =
  let rec aux ctx =
    match ctx with
      | [] -> nil
      | [last] when tc [] last = olistty -> last
      | head::tail -> app cons [head; aux tail]
  in
    aux (List.rev ctx)

let wellformed ctx =
  let rec aux = function
    | [] -> true
    | head::tail ->
        let ty = tc [] head in
          (ty = oty && aux tail) || (ty = olistty && tail = [])
  in
    aux (List.rev ctx)

let extract_singleton ctx =
  match ctx with
    | [e] -> e
    | [] -> failwith "Contexts did not match"
    | _ -> failwithf "Contexts did not match: %s" (context_to_string ctx)

(* For each context pair (ctx1, ctx2), make ctx2 a subcontext of ctx1 *)
let reconcile pair_list =
  let pair_list = List.map (fun (x,y) -> xor x y) pair_list in
  let pair_list = List.remove_all (fun (_x,y) -> is_empty y) pair_list in
  let var_ctx_list =
    List.map (fun (x,y) -> (extract_singleton x, y)) pair_list
  in
  let groups = group var_ctx_list in
  let groups = List.map (fun (x,y) -> (x, union_list y)) groups in
  let groups = List.map (fun (x,y) -> (x, normalize y)) groups in
  List.iter begin fun (var, ctx) ->
    Unify.right_unify var (context_to_term ctx)
  end groups

(* Want to make hctx as large as possible but remain a subcontext of gctx *)
let backchain_reconcile hctx gctx =
  let hctx, gctx = xor hctx gctx in
    match hctx with
      | [hv] -> Unify.right_unify hv (context_to_term gctx)
      | [] -> ()
      | _ -> failwith ("Contexts did not match: " ^ (context_to_string hctx))
