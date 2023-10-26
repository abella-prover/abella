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

exception Is_prop
let ensure_not_prop aty =
  if aty = propaty then raise Is_prop

let contains_prop ty =
  match iter_ty ensure_not_prop ty with
  | () -> false
  | exception Is_prop -> true

type non_wff_reason =
  | Nonstrat of id
  | Ho_args of (id * ty) list
exception Non_wff of non_wff_reason

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

let check_well_formed ~def =
  let check_clause clauseno {head ; body} =
    let clauseno = clauseno + 1 in
    let nonposities = get_pred_occurrences body in
    let is_ho_var (v, ty) = if contains_prop ty then Some (v, ty) else None in
    let ho_names = def_head_args head |>
                   capital_tids |>
                   List.filter_map is_ho_var in
    let scan () =
      if ho_names <> [] then raise (Non_wff (Ho_args ho_names)) ;
      Iset.iter begin fun pname ->
        if Itab.mem pname def.mutual then
          raise (Non_wff (Nonstrat pname)) ;
      end nonposities in
    try scan () with
    | Non_wff reason ->
        let msg = match reason with
          | Nonstrat name ->
              Printf.sprintf
                "Definition might not be stratified\n\
               \ (%S occurs to the left of -> in clause #%d)"
                name clauseno
        | Ho_args vtys ->
            let msgs =
              List.map begin fun (v, ty) ->
                Printf.sprintf "  %s : %s" v (ty_to_string ty)
              end vtys |> String.concat "\n"
            in
            Printf.sprintf
              "Definition might not be well-formed because of the following\n\
               higher-order parameters in clause #%d:\n" clauseno
            ^ msgs
        in
        if stratification_warnings_are_errors then failwith msg
        else Output.msg_printf ("" ^^ "Warning: %s\n%!") msg
  in
  List.iteri check_clause def.clauses

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
  check_well_formed ~def

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
