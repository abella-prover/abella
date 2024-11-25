(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2024  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Extensions
open Term
open Metaterm
open Abella_types

let format_guard ff guard =
  let format_term ff t = Term.format_term ff t in
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

(** [evaluate_guard guard t] returns true if the guard stops compute *)
let evaluate_guard guard t =
  let format_term ff t = Term.format_term ff t in
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
  let pred, _args =
    match Term.term_head atm with
    | Some pa -> pa
    | None -> bugf "Invalid predicate: %s" (term_to_string atm)
  in
  Term.term_to_name pred
  |> Hashtbl.find_all guards
  |> List.exists (fun guard -> evaluate_guard guard atm)

(******************************************************************************)
(* Compute implementation *)

let () =
  let open Typing in
  let e = UCon (ghost_pos, "X", fresh_tyvar ()) in
  let l = UCon (ghost_pos, "L", fresh_tyvar ()) in
  let head = UApp (ghost_pos,
                   UApp (ghost_pos,
                         UCon (ghost_pos, "member", fresh_tyvar ()),
                         e),
                   l) in
  let test = ["L"] in
  make_guard ~head ~test |> add_guard

type compute_hyp = {
  clr : clearable ;
  form : metaterm ;
}

type compute_wait = {
  vars : (id * term) list ;
  chyp : compute_hyp ;
}

let ch_to_string (ch : compute_hyp) = clearable_to_string ch.clr

let format_ch ff (ch : compute_hyp) =
  Format.fprintf ff "%s : %a" (clearable_to_string ch.clr) format_metaterm ch.form

let cw_to_string w =
  Printf.sprintf "<%s>%s"
    (List.map fst w.vars |> String.concat ", ")
    (ch_to_string w.chyp)

let pp_print_wait_var ff (v, t) =
  Format.fprintf ff "%s <- %s" v (term_to_string t)

let get_wait clr form =
  let vars = get_metaterm_used form in
  { vars ; chyp = { clr ; form } }

let is_unchanged wait =
  List.for_all (fun (_, t) -> Term.is_free t) wait.vars

exception Out_of_gas
exception Suspended

let compute ?name ?(gas = 1_000) hs =
  let v, kind = 0, "compute" in
  let total_gas = gas in
  let gas = ref total_gas in
  let fresh_compute_hyp =
    let count = ref @@ -1 in
    fun () -> incr count ; "<#" ^ string_of_int !count ^ ">"
  in
  let subgoals = ref [] in
  let rec compute_all ~chs ~wait ~todo =
    Output.trace ~v begin fun (module Trace) ->
      Trace.printf ~kind
        "compute_all ~chs:[%s] ~wait:[%s] ~todo:[%s]"
        (List.map ch_to_string chs |> String.concat ",")
        (List.map cw_to_string wait |> String.concat ",")
        (List.map ch_to_string todo |> String.concat ",")
    end ;
    match todo with
    | [] ->
        let sg =
          List.iter begin fun ch ->
            Output.trace ~v begin fun (module Trace) ->
              Trace.printf ~kind "Renaming: %s" (ch_to_string ch)
            end ;
            let stmt = Prover.get_stmt_clearly ch.clr in
            Prover.add_hyp ?name stmt
          end chs ;
          let state = Term.get_bind_state () in
          let current_seq = Prover.copy_sequent () in
          fun () ->
            Term.set_bind_state state ;
            Prover.set_sequent current_seq
        in
        subgoals := sg :: !subgoals ;
    | h :: todo ->
        compute_one ~chs ~wait ~todo h
  and compute_one ~chs ~wait ~todo (ch : compute_hyp) =
    let suspend () = compute_all ~chs ~wait:(get_wait ch.clr ch.form :: wait) ~todo in
    let doit () = compute_case ~chs ~wait ~todo ch in
    match ch.form with
    | Binding (Forall, _, _)
    | Arrow _ ->
        suspend ()
    | Obj ({ mode = Async ; right = atm ; _ }, _)
    | Pred (atm, _)
      when is_guarded atm ->
        suspend ()
    | Obj ({ mode = Sync f ; _ }, _) -> begin
        match Term.(observe @@ hnorm f) with
        | Var _ -> suspend ()
        | _ -> doit ()
      end
    | _ -> doit ()
  and compute_case ~chs ~wait ~todo (ch : compute_hyp) =
    if !gas <= 0 then raise Out_of_gas ;
    let saved = Prover.copy_sequent () in
    match Prover.case_subgoals ch.clr with
    | exception _ ->
        Prover.set_sequent saved ;
        compute_all ~chs ~wait:(get_wait ch.clr ch.form :: wait) ~todo
    | cases ->
        let chs = List.filter (fun oldch -> oldch.clr <> ch.clr) chs in
        let saved = Prover.copy_sequent () in
        List.iter begin fun case ->
          Prover.set_sequent saved ;
          Output.trace ~v begin fun (module Trace) ->
            Trace.format ~kind "Case %a" format_ch ch
          end ;
          List.iter Prover.add_if_new_var case.Tactics.new_vars ;
          let hs = List.map (fun h -> Prover.unsafe_add_hyp (fresh_compute_hyp ()) h) case.new_hyps in
          Term.set_bind_state case.bind_state ;
          Prover.update_self_bound_vars () ;
          Output.trace ~v begin fun (module Trace) ->
            List.iter begin fun h ->
              Trace.format ~kind "Adding: %s : %a" h.Prover.id format_metaterm h.term
            end hs
          end ;
          decr gas ;
          let (wait, newly_active) = List.partition is_unchanged wait in
          Output.trace ~v begin fun (module Trace) ->
            List.iter begin fun w ->
              Trace.format ~kind "Reactivated %s: %a cuz @[<v1>%a@]"
                (clearable_to_string w.chyp.clr) format_metaterm w.chyp.form
                (Format.pp_print_list pp_print_wait_var) w.vars
            end newly_active
          end ;
          let new_chs = List.rev_map (fun h -> { clr = Remove (h.Prover.id, []) ; form = h.term }) hs in
          let chs = List.rev_append new_chs chs in
          let todo =
            List.rev_map (fun w -> w.chyp) newly_active
            @ new_chs @ todo in
          compute_all ~chs ~wait ~todo
        end cases
  in
  let todo = List.map (fun h -> { clr = h ; form = Prover.get_hyp_or_lemma (Prover.stmt_name h) }) hs in
  match compute_all ~chs:[] ~wait:[] ~todo with
  | exception Out_of_gas ->
      failwithf "Compute ran out of gas (given %d) -- looping?" total_gas
  | _ ->
      Prover.add_subgoals @@ List.rev !subgoals ;
      Prover.next_subgoal ()
