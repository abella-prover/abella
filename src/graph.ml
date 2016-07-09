(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2016 Inria (Institut National de Recherche            *)
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

open Extensions
open Unifyty
open Term

type t = (aty * aty) list

let empty = []

let add_arc arcs a b =
  if List.mem (a, b) arcs then arcs else (a, b)::arcs

let arc_predecessor (s, t) a =
  assert (not (contains_tyvar (tybase a)));
  let a' = tybase a in
  let s' = tybase s in
  let t' = tybase t in
  try
    let tysub = 
      unify_constraints [(t', a', (ghost, CArg))] in
    let s'' = apply_sub_ty tysub s' in
    if (contains_tyvar s'') then
        failwithf "Subordination check failure: in '%s',\
                  \ the source type cannot be fully determined by\
                  \ the target type\n" (ty_to_string (tyarrow [s'] t'))
    else
      match s'' with
      | Ty([], aty) -> Some aty
      | _ -> failwithf "Subordination check failure: new non-atomic\
               \ type %s arises during subordination check\n"
         (ty_to_string s'')
  with
  | TypeInferenceFailure _ -> None
  | e -> raise e
  
let direct_predecessors arcs a =
  assert (not (contains_tyvar (tybase a)));
  let infer_pred preds (s,t) =
    match (arc_predecessor (s,t) a) with
    | Some aty -> (aty, (s,t)) :: preds
    | None -> preds
  in
  List.fold_left infer_pred [] arcs

(* search the predecessors of a in the graph arcs.
   a must be a ground atomic type *)
let predecessors arcs a =
  (* aux accumulates pairs of nodes (atomic types) and paths from the
     root to the nodes by performing depth first search *)
  let rec aux acc (a,path) =
    if List.mem a (List.map fst acc) then
      acc
    else
      let dpreds = (direct_predecessors arcs a) in
      (* abandon the search if an arc is used more than once in any
         search path. This is a conservative measure to make sure that
         the search always termintates in presence of polymorphic types. *)
      let check_no_arc_reused path arc =
        if List.mem arc path then
          failwith "Subordination check failure: \
                    \ subordination relation may be infinite\n"
      in
      List.iter (check_no_arc_reused path) (List.map snd dpreds);
      let dpreds = List.map (fun (a,e) -> (a, e::path)) dpreds in
      List.fold_left aux ((a,path)::acc) dpreds
  in
  assert (not (contains_tyvar (tybase a)));
  let acc = aux [] (a,[]) in
  List.map fst acc

let is_path arcs a b =
  assert (not (contains_tyvar (tybase a)));
  assert (not (contains_tyvar (tybase b)));
  List.mem a (predecessors arcs b)
