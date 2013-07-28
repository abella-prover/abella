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

open Term
open Extensions

type sr = string Graph.t * string list

let empty = (Graph.empty, [])

let head (Ty(_, h)) = h

let close (graph, closed) atys =
  let closed = atys @ closed in
    List.iter
      (fun aty ->
         match List.minus (Graph.predecessors graph aty) closed with
           | [] -> ()
           | xs -> failwith
               (Printf.sprintf "Cannot close %s without closing %s"
                  aty (String.concat ", " xs)))
      atys ;
    (graph, closed)

let query (graph, closed) a b =
  Graph.is_path graph (head a) (head b) || not (List.mem (head b) closed)

let add (graph, closed) a b =
  if List.mem b closed then
    if Graph.is_path graph a b then
      (graph, closed)
    else
      failwithf "Type %s is closed and cannot be subordinated by %s" b a
  else
    (Graph.add_arc graph a b, closed)

let update sr ty =
  let rec aux sr (Ty(args, target)) =
    let sr = List.fold_left aux sr args in
      List.fold_left (fun sr ty -> add sr (head ty) target) sr args
  in
    aux sr ty

let ensure (graph, _) ty =
  let rec aux (Ty(args, target)) =
    List.iter aux args ;
    let target_preds = Graph.predecessors graph target in
      List.iter
        (fun aty ->
           if not (List.mem (head aty) target_preds) then
             failwith
               (Printf.sprintf
                  "Type %s cannot be made subordinate to %s without explicit declaration"
                  (head aty) target))
        args ;
  in
    aux  ty

let subordinates (graph, closed) a =
  Graph.predecessors graph a
