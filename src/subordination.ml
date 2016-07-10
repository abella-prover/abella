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

open Term
open Extensions

type sr = Graph.t * aty list

let empty = (Graph.empty, [])

let check_non_poly a =
  (if contains_tyvar (tybase a) then
    failwithf "Subordination relation cannot be inferred for plymorphic types: %s"
      (aty_to_string a))

let head (Ty(_, a)) = a

let close (graph, closed) atys =
  List.iter check_non_poly atys;
  let closed = atys @ closed in
    List.iter
      (fun aty ->
         match List.minus (Graph.predecessors graph aty) closed with
           | [] -> ()
           | xs -> failwith
               (Printf.sprintf "Cannot close %s without closing %s"
                  (aty_to_string aty) 
                  (String.concat ", " (List.map aty_to_string xs))))
      atys ;
    (graph, closed)

let query (graph, closed) a b =
  contains_tyvar b || contains_tyvar a || 
  not (List.mem (head b) closed) || Graph.is_path graph (head a) (head b)

let replace_tyvars_for_params ty =
  let typarams = get_tycstr (fun s -> is_capital_name s || is_gen_tyvar s) ty in
  let tysub = List.map (fun p -> (p, fresh_tyvar ())) typarams in
  apply_sub_ty tysub ty

let rec mark_gen_tyvar gen_tyvars ty =
  let aux = mark_gen_tyvar gen_tyvars in
  match ty with
  | Ty (tys, AtmTy(cty, args)) ->
     let tys' = List.map aux tys in
     let args' = List.map aux args in
     let cty' = if List.mem cty gen_tyvars 
       then tag_gen_tyvar cty else cty in
     Ty (tys', AtmTy(cty', args'))
  
(* check that the arc does not extend the existing subordination relation *)
let check_no_sr_extension closed a b =
  List.iter begin fun aty -> 
    match Graph.arc_predecessor (a,b) aty with
    | None -> ()
    | Some t -> 
       if not (List.mem t closed) then
         failwithf "Type %s is closed and cannot be subordinated by %s"
           (aty_to_string aty) (aty_to_string t)
  end closed

let add (graph, closed) a b =
  check_no_sr_extension closed a b;
  (Graph.add_arc graph a b, closed)

let update sr ty =
  let ty = replace_tyvars_for_params ty in
  let rec aux sr (Ty(args, target)) =
    let sr = List.fold_left aux sr args in
      List.fold_left (fun sr ty -> add sr (head ty) target) sr args
  in
    aux sr ty

let ensure (graph, closed) ty =
  let ty = replace_tyvars_for_params ty in
  let rec aux (Ty(args, target)) =
    List.iter aux args;
    List.iter begin fun arg -> 
      check_no_sr_extension closed (head arg) target
    end args
  in
  aux ty

let subordinates (graph, closed) a =
  check_non_poly a;
  Graph.predecessors graph a
