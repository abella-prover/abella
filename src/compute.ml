(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2024  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

[@@@ocaml.warning "-27"]

open! Extensions
open! Term
open! Metaterm

type guard = {
  predicate : id ;
  pattern : term ;
  condition : term list ;
}

let make_guard ~head ~test =
  let (predicate, pattern) =
    let rec get_predicate : Typing.uterm -> _ = function
      | UCon (_, pred, _) -> pred
      | UApp (_, ut, _) -> get_predicate ut
      | ULam _ ->
          failwith "Invalid lambda-abstraction in guard pattern"
    in
    (get_predicate head, head)
  in
  let vids = Typing.(uterms_extract_if is_capital_name [pattern]) in
  let tyctx = Typing.ids_to_fresh_tyctx vids in
  let (ty, eqns) = Typing.(infer_type_and_constraints ~sign:!sign tyctx pattern) in
  Unifyty.unify_constraints eqns ;
  let vars = List.map (fun (id, ty) -> (id, Term.fresh ~tag:Eigen 0 ty)) tyctx in
  let pattern = Typing.(uterm_to_term pattern |> replace_term_vars vars) in
  if not @@ Term.(eq_ty ty propty || eq_ty ty oty) then
    failwithf "Expected target type prop or o, got %s" (ty_to_string ty) ;
  let condition =
    List.unique test
    |> List.map begin fun vid ->
      match List.assoc_opt vid vars with
      | None -> failwithf "Unknown condition variable %s" vid
      | Some term -> term
    end
  in
  { predicate ; pattern ; condition }

open struct
  let format_term ff t = Term.format_term ff t
end

let format_guard ff guard =
  Format.fprintf ff "Suspend %a := @[<hov0>%a@]"
    (format_term) guard.pattern
    (Format.pp_print_list format_term
       ~pp_sep:Format.pp_print_commaspace) guard.condition

let guard_to_string guard =
  let buf = Buffer.create 19 in
  let ff = Format.formatter_of_buffer buf in
  format_guard ff guard ;
  Format.pp_print_flush ff () ;
  Buffer.contents buf

(** [evaluate_guard guard t] returns true if the guard stops compute *)
let evaluate_guard guard t =
  let v, kind = 2, "evaluate_guard" in
  Output.trace ~v begin fun (module Trace) ->
    Trace.format ~kind "@[<v0>Testing @[%a@]@,against @[%a@]@]"
      format_term t
      format_guard guard
  end ;
  let state = Term.get_scoped_bind_state () in
  let result = try
      Unify.left_unify t guard.pattern ;
      Output.trace ~v begin fun (module Trace) ->
        Trace.format ~kind "Unification resulted in %a"
          format_term guard.pattern
      end ;
      (* all test vars neeed to be eigen to stop *)
      List.for_all Term.has_eigen_head guard.condition
    with _ -> false
  in
  Term.set_scoped_bind_state state ;
  Output.trace ~v begin fun (module Trace) ->
    Trace.printf ~kind "result: %b" result
  end ;
  result

let guards : (id, guard) Hashtbl.t = State.table ()

let add_guard (gd : guard) = Hashtbl.add guards gd.predicate gd

let is_guarded atm =
  let pred, args =
    match Term.(observe (hnorm atm) |> term_head) with
    | Some pa -> pa
    | None -> bugf "Invalid predicate: %s" (term_to_string atm)
  in
  Term.term_to_name pred
  |> Hashtbl.find_all guards
  |> List.exists (fun guard -> evaluate_guard guard atm)
