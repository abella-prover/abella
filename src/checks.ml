(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015-2018  Inria (Institut National de Recherche
 *                          en Informatique et en Automatique)
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
  ensure_no_restrictions (umetaterm_to_metaterm term)

let contains_prop ty =
  let cp = ref false in
  iter_ty
    (fun bty ->
       if bty = propaty then cp := true)
    ty;
  !cp

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
  iter_preds begin fun ~parity:_ ~posity t ->
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

let check_theorem tys thm =
  let tys' = metaterm_collect_gentyvar_names thm in
  if List.minus tys' tys <> [] then
    failwith "Some type variables in the theorem is not bounded";
  ensure_no_restrictions thm

let check_noredef ids =
  let (_, ctable) = !sign in
  List.iter begin fun id ->
    if List.mem id (List.map fst ctable) then
      failwithf "Predicate or constant %s already exists" id
  end ids

let ensure_not_capital name =
  if is_capital_name name then
    failwithf "Invalid defined predicate name %S.\n\
             \ Defined predicates may not begin with a capital letter."
      name

let ensure_wellformed_head t =
  match t with
  | Pred _ -> ()
  | Binding(Nabla, _, Pred _) -> ()
  | _ ->
      failwithf "Invalid head in definition: %s"
        (metaterm_to_string t)

let check_basic_stratification ~def =
  let check_clause {head ; body} =
    let nonposities = get_pred_occurrences body in
    let is_ho_var arg =
      match observe (hnorm arg) with
      | Var { Term.ty = ty; Term.name = v; _ } when contains_prop ty -> Some v
      | _ -> None
    in
    let ho_names = def_head_args head |>
                   List.filter_map is_ho_var in
    let scan () = Iset.iter begin fun pname ->
        if Itab.mem pname def.mutual then
          raise (Nonstrat (Negative_head pname)) ;
        if List.mem pname ho_names then
          raise (Nonstrat (Negative_ho_arg pname)) ;
      end nonposities in
    try scan () with
    | Nonstrat reason ->
        let msg = match reason with
          | Negative_head name ->
              Printf.sprintf
                "Definition might not be stratified\n\
               \ (%S occurs to the left of ->)"
                name
          | Negative_ho_arg name ->
              Printf.sprintf
                "Definition can be used to defeat stratification\n\
               \ (higher-order argument %S occurs to the left of ->)"
                name
        in
        if stratification_warnings_are_errors then failwith msg
        else Printf.fprintf !out "Warning: %s\n%!" msg
  in
  List.iter check_clause def.clauses

let check_stratification ~def =
  check_basic_stratification ~def

let check_def ~def =
  Itab.iter (fun nm _ -> ensure_not_capital nm) def.mutual ;
  List.iter begin fun {head ; body} ->
    let head_pred = def_head_name head in
    ensure_wellformed_head head ;
    if not (Itab.mem head_pred def.mutual) then
      failwithf "Found stray clause for %s" head_pred ;
    ensure_no_restrictions head ;
    ensure_no_restrictions body ;
  end def.clauses ;
  check_stratification ~def

(** The list of type parameters of a definition must be 
    exactly those occuring in the type of the constants being defined *)
let check_typaram tyvars ty =
  let tyvars' = get_typaram ty in
  let extra1 = (List.minus tyvars tyvars') in
  let extra2 = (List.minus tyvars' tyvars) in
  if (List.length extra1 <> 0 || List.length extra2 <> 0) then
    failwithf "Some type parameters do not occur in type of some constant being defined"

let check_typarams tyvars tys =
  List.iter (check_typaram tyvars) tys

(* Check that there is no parameterization of types at clause levels *)
let ensure_no_schm_clause typarams cl =
  let htyvars = (metaterm_collect_gentyvar_names cl.head) in
  let btyvars = (metaterm_collect_gentyvar_names cl.body) in
  [] = (List.minus (htyvars @ btyvars) typarams)

let ensure_no_schm_clauses typarams clauses =
  let ns = List.for_all (ensure_no_schm_clause typarams) clauses in
  if not ns then
    failwithf "Type variables in some clause are not bound at the \
               definition level"
