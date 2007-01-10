(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006 Nadathur, Linnell, Baelde, Ziegler                    *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

open Term
open Format

exception Found of int

type assoc = Left | Right | Both | No
  
(* List of infix operators sorted by priority. *)
let infix : (string * assoc) list ref = ref []
let set_infix l = infix := l
let is_infix x = List.mem_assoc x !infix
let get_assoc op = List.assoc op !infix
let priority x =
  try
    ignore (List.fold_left
              (fun i (e, assoc) -> if e = x then raise (Found i) else i+1)
              1 !infix) ;
    0
  with
    | Found i -> i
let get_max_priority () = List.length !infix

(* Support for object level logic *)
let is_obj_quantifier x = x = "pi" || x = "sigma"

(* Generic output function *)

let tag2str = function
  | Constant -> "c"
  | Eigen -> "e"
  | Logic -> "l"

let parenthesis x = "(" ^ x ^ ")"
let bracket x = "{" ^ x ^ "}"

let rec list_range a b =
  if a > b then [] else a::(list_range (a+1) b)

let term_to_string term =
  let term = Norm.deep_norm term in
  let high_pr = 2 + get_max_priority () in
  let pre = getAbsName () in
  let pp_var x = pre ^ (string_of_int x) in
  let rec pp pr n term =
    match observe term with
      | Var v -> Printf.sprintf "%s" v.name
      | DB i -> pp_var (n-i+1)
      | App (t,ts) ->
          begin match observe t, ts with
            | Var {name=op; tag=Constant}, [a; b] when is_infix op ->
                let op_p = priority op in
                let assoc = get_assoc op in
                let pr_left, pr_right = begin match assoc with
                  | Left -> op_p, op_p+1
                  | Right -> op_p+1, op_p
                  | _ -> op_p, op_p
                  end in
                let res =
                  (pp pr_left n a) ^ " " ^ op ^ " " ^ (pp pr_right n b)
                in
                  if op_p >= pr then res else parenthesis res
            | Var {name=op; tag=Constant}, [a] when is_obj_quantifier op ->
                op ^ " " ^ (pp 0 n a)
            | _ ->
                let res =
                  String.concat " " (List.map (pp high_pr n) (t::ts))
                in
                  if pr < high_pr then res else parenthesis res
          end
      | Lam (0,t) -> assert false
      | Lam (i,t) ->
          let res = ((String.concat "\\"
                       (List.map pp_var (list_range (n+1) (n+i)))) ^ "\\" ^
                      (pp 0 (n+i) t)) in
            if pr == 0 then res else parenthesis res
      | Ptr t -> assert false (* observe *)
      | Susp _ -> assert false (* deep_norm *)
 in
    pp 0 0 term

let pp_term out term = fprintf out "%s" (term_to_string term)

(* Output to stdout *)
let print_term term = printf "%s" (term_to_string term)
