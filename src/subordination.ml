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

open Term
open Extensions

type sr = Graph.t * aty list

let empty = (Graph.empty, [])

let ty_no_tyvar ty =
  (not (ty_contains_tyvar ty)) && (not (ty_contains_gentyvar ty))

let check_non_poly a =
  if not (ty_no_tyvar (tybase a)) then
    failwithf "Subordination relation cannot be inferred for plymorphic types: %s"
      (aty_to_string a)

let check_no_tyvar ty =
  assert (not (ty_contains_tyvar (tybase ty)))

let head ty =
  match observe_ty ty with
  | (Ty(_, a)) -> a

let aty_is_var = function
  | Tygenvar _ | Typtr _ -> true
  | Tycons _ -> false

let close (graph, closed) atys =
  List.iter check_non_poly atys;
  let closed = atys @ closed in
    List.iter
      (fun aty ->
         match List.minus ~cmp:eq_aty (Graph.predecessors graph aty) closed with
           | [] -> ()
           | xs -> failwith
               (Printf.sprintf "Cannot close %s without closing %s"
                  (aty_to_string aty)
                  (String.concat ", " (List.map aty_to_string xs))))
      atys ;
    (graph, closed)

let query (graph, closed) a b =
  not (ty_no_tyvar a) || not (ty_no_tyvar b) ||
  not (List.mem ~cmp:eq_aty (head b) closed) || Graph.is_path graph (head a) (head b)

(* check that the arc does not extend the existing subordination relation *)
let check_no_sr_extension graph closed a b =
  (* A variable target carries no subordination information; skip it.
     (A variable source is still meaningful, e.g. A -> list A.) *)
  if aty_is_var b then () else begin
  let graph' = Graph.add_arc graph a b in
  List.iter begin fun aty ->
    let before = Graph.predecessors graph aty in
    let after = Graph.predecessors graph' aty in
    match List.minus ~cmp:eq_aty after before with
    | [] -> ()
    | xs ->
        failwithf "Type %s is closed and cannot be subordinated by %s"
          (aty_to_string aty)
          (String.concat ", " (List.map aty_to_string xs))
  end closed
  end

let add (graph, closed) a b =
  check_no_tyvar a;
  check_no_tyvar b;
  (* Arcs with a variable target carry no subordination information
     and would only poison predecessor queries, so skip them. *)
  if aty_is_var b then (graph, closed) else begin
  check_no_sr_extension graph closed a b;
  (Graph.add_arc graph a b, closed)
  end

let update sr ty =
  let rec aux sr ty =
    match observe_ty ty with
    | Ty(args, target) ->
        let sr = List.fold_left aux sr args in
        List.fold_left (fun sr ty -> add sr (head ty) target) sr args
  in
  aux sr ty

let ensure (graph, closed) ty =
  let rec aux ty =
    match observe_ty ty with
    | Ty(args, target) ->
        List.iter aux args;
        List.iter begin fun arg ->
          check_no_sr_extension graph closed (head arg) target
        end args
  in
  aux ty

let subordinates (graph, _closed) a =
  check_non_poly a;
  Graph.predecessors graph a
