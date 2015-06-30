(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* BEGIN global Abella configuration *)

let stratification_warnings_are_errors = false
  (** Any stratification violation warnings are treated as errors *)

(* END global Abella configuration *)

open Term
open Metaterm
open Abella_types
open Typing

open Extensions

let out = ref stdout

(* Checks *)

let get_restriction r =
  match r with
  | Smaller n -> n
  | CoSmaller n -> n
  | Equal n -> n
  | CoEqual n -> n
  | Irrelevant -> 0

let get_max_restriction t =
  let rec aux t =
    match t with
    | True | False | Eq _ -> 0
    | Obj(_, r) -> get_restriction r
    | Arrow(a, b) -> max (aux a) (aux b)
    | Binding(_, _, body) -> aux body
    | Or(a, b) -> max (aux a) (aux b)
    | And(a, b) -> max (aux a) (aux b)
    | Pred(_, r) -> get_restriction r
  in
  aux t

let ensure_no_restrictions term =
  if get_max_restriction term > 0 then
    failwithf "Invalid formula: %s\n\
             \ Cannot use size restrictions (*, @, #, or +)"
      (metaterm_to_string term)

let untyped_ensure_no_restrictions term =
  ensure_no_restrictions (umetaterm_to_metaterm [] term)

let rec contains_prop ty =
  match ty with
  | Ty (argtys, targty) ->
      targty = "prop" || List.exists contains_prop argtys

type nonstrat_reason =
  | Negative_head of string
  | Negative_ho_arg of string
exception Nonstrat of nonstrat_reason

let add_sgn preds p posity =
  let old_posity =
    try Itab.find p preds with Not_found -> posity in
  let posity =
    if old_posity = posity then posity
    else NONPOS
  in
  Itab.add p posity preds

let get_pred_occurrences mt =
  let preds = ref Iset.empty in
  let rec aux_term t =
    match observe (hnorm t) with
    | Var v when contains_prop v.ty ->
        preds := Iset.add v.Term.name !preds
    | App (t, ts) ->
        aux_term t ; List.iter aux_term ts
    | Lam (_, t) ->
        aux_term t
    | Var _ | DB _ -> ()
    | _ -> assert false
  in
  iter_preds begin fun ~parity ~posity t ->
    if posity = NONPOS then aux_term t
  end mt ;
  !preds

let warn_stratify names head term =
  let nonposities = get_pred_occurrences term in
  let is_ho_var arg =
    match observe (hnorm arg) with
    | Var { Term.ty = ty; Term.name = v; _ } when contains_prop ty -> Some v
    | _ -> None
  in
  let ho_names =
    def_head_args head |>
    List.filter_map is_ho_var in
  let doit () =
    Iset.iter begin fun pname ->
      if List.mem pname names then
        raise (Nonstrat (Negative_head pname)) ;
      if List.mem pname ho_names then
        raise (Nonstrat (Negative_ho_arg pname)) ;
    end nonposities
  in
  try doit () with
  | Nonstrat reason ->
      let msg = match reason with
        | Negative_head name ->
            Printf.sprintf
              "Definition might not be stratified\n  (%S occurs to the left of ->)"
              name
        | Negative_ho_arg name ->
            Printf.sprintf
              "Definition can be used to defeat stratification\n  (higher-order argument %S occurs to the left of ->)"
              name
      in
      if stratification_warnings_are_errors
      then failwith msg
      else Printf.fprintf !out "Warning: %s\n%!" msg

let check_theorem thm =
  ensure_no_restrictions thm

let check_noredef ids =
  let (_, ctable) = !sign in
  List.iter begin fun id ->
    if not (List.mem id [k_fresh ; k_name]) &&
       List.mem id (List.map fst ctable)
    then failwithf "Predicate or constant %s already exists" id
  end ids

let ensure_not_capital name =
  if is_capital_name name then
    failwithf "Invalid defined predicate name %S.\n\
             \ Defined predicates may not begin with a capital letter."
      name

let ensure_name_contained id ids =
  if not (List.mem id ids) then
    failwithf "Found stray clause for %s" id

let ensure_wellformed_head t =
  match t with
    | Pred _ -> ()
    | Binding(Nabla, _, Pred _) -> ()
    | _ ->
        failwithf "Invalid head in definition: %s"
          (metaterm_to_string t)

let check_def_clauses names defs =
  List.iter ensure_not_capital names ;
  List.iter
    (fun {head ; body} ->
       ensure_wellformed_head head ;
       ensure_name_contained (def_head_name head) names ;
       ensure_no_restrictions head ;
       ensure_no_restrictions body ;
       warn_stratify names head body)
    defs
