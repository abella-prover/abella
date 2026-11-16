(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2024  Inria (Institut National de Recherche
 *                            en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

open Term
open Typing
open Metaterm
open Abella_types
open Extensions

module P = Prover_imm

type compute_error =
  | Compute_stmt of P.stmt_error
  | Compute_rename of P.rename_hint_error
  | Compute_out_of_gas of int
  | Compute_tactic_failure of string

(* Internal fuel exhaustion; mapped to [Compute_out_of_gas]
   at the boundary. *)
exception Out_of_gas

type compute_hyp = {
  clr : clearable ;
  form : metaterm ;
}

type compute_wait = {
  vars : (id * term) list ;
  chyp : compute_hyp ;
}

let is_free t =
  match Term.observe t with
  | Var { tag = Eigen ; _ } -> true
  | _ -> false

let is_unchanged wait =
  List.for_all (fun (_, t) -> is_free t) wait.vars

let get_wait clr form =
  let vars = get_metaterm_used form in
  { vars ; chyp = { clr ; form } }

(* [Prover.case_subgoals] on an explicit sequent. Raises like
   the original; [compute_case] suspends on [Failure] and
   [Unify.UnifyFailure] exactly as [Compute] does. *)
let case_subgoals sq clr =
  let global_support =
    List.flatten_map metaterm_support
      (List.map (fun (h : P.hyp) -> h.P.term) sq.P.hyps)
    @ metaterm_support sq.P.goal
  in
  let sq, term =
    match P.get_stmt_clearly sq clr with
    | Ok x -> x
    | Error _ ->
        failwith "compute: cannot resolve case statement"
  in
  let mutual, defs = Prover.def_unfold term in
  let state = Term.get_scoped_bind_state () in
  try
    ( sq,
      Tactics.case ~used:sq.P.vars ~sr:!sr
        ~clauses:!Prover.clauses ~mutual ~defs
        ~global_support term )
  with e ->
    Term.set_scoped_bind_state state ;
    raise e

let compute sq ?hint ?(gas = 1_000) hs =
  let total_gas = gas in
  let gas = ref total_gas in
  let leaf_count = ref 0 in
  let fresh_compute_hyp =
    let count = ref @@ -1 in
    fun () ->
      incr count ;
      "<#" ^ string_of_int !count ^ ">"
  in
  let base = sq in
  let rec compute_all sq ~chs ~wait ~todo =
    match todo with
    | [] -> finish_branch sq chs
    | h :: todo -> compute_one sq ~chs ~wait ~todo h
  and compute_one sq ~chs ~wait ~todo ch =
    let suspend () =
      compute_all sq ~chs
        ~wait:(get_wait ch.clr ch.form :: wait)
        ~todo
    in
    let doit () = compute_case sq ~chs ~wait ~todo ch in
    match ch.form with
    | Binding (Forall, _, _)
    | Arrow _ ->
        suspend ()
    | Obj ({ mode = Async ; right = atm ; _ }, _)
    | Pred (atm, _)
      when Compute.is_guarded atm ->
        suspend ()
    | Obj ({ mode = Sync f ; _ }, _) -> begin
        match Term.(observe @@ hnorm f) with
        | Var _ -> suspend ()
        | _ -> doit ()
      end
    | _ -> doit ()
  and compute_case sq ~chs ~wait ~todo ch =
    if !gas <= 0 then raise Out_of_gas ;
    match case_subgoals sq ch.clr with
    | exception (Failure _ | Unify.UnifyFailure _) ->
        compute_all sq ~chs
          ~wait:(get_wait ch.clr ch.form :: wait)
          ~todo
    | sq, cases ->
        let chs =
          List.filter (fun oldch -> oldch.clr <> ch.clr) chs
        in
        List.fold_left
          (fun acc case ->
            match acc with
            | Result.Error _ as e -> e
            | Result.Ok subs -> begin
                match branch sq ch case ~chs ~wait ~todo with
                | Result.Error _ as e -> e
                | Result.Ok branch_subs ->
                    Result.ok (subs @ branch_subs)
              end)
          (Result.ok []) cases
  and branch sq _ch case ~chs ~wait ~todo =
    let sq, new_chs =
      List.fold_left
        (fun (sq, chs) h ->
          let name = fresh_compute_hyp () in
          let sq = P.unsafe_add_hyp sq name h in
          let ch = { clr = Remove (name, []) ; form = h } in
          (sq, ch :: chs))
        (sq, []) case.Tactics.new_hyps
    in
    let new_chs = List.rev new_chs in
    let sq =
      List.fold_left
        (fun sq v -> P.add_if_new_var sq v)
        sq case.Tactics.new_vars
    in
    (* Install the case bind state before the
       dereference-sensitive update, mirroring [Compute]. *)
    Term.set_bind_state case.Tactics.bind_state ;
    let sq = P.update_self_bound_vars sq in
    decr gas ;
    let wait, newly_active =
      List.partition is_unchanged wait
    in
    let chs = List.rev_append new_chs chs in
    let todo =
      List.rev_map (fun w -> w.chyp) newly_active
      @ new_chs @ todo
    in
    compute_all sq ~chs ~wait ~todo
  and finish_branch sq chs =
    let idx = !leaf_count in
    incr leaf_count ;
    let alt = Prover.alt_for_subgoal hint idx in
    let res =
      List.fold_left
        (fun acc ch ->
          match acc with
          | Result.Error _ as e -> e
          | Result.Ok sq -> begin
              match P.get_stmt_clearly sq ch.clr with
              | Result.Error e ->
                  Result.error (Compute_stmt e)
              | Result.Ok (sq, stmt) ->
                  Result.ok (P.add_hyp_with_hint sq alt stmt)
            end)
        (Result.ok sq) chs
    in
    match res with
    | Result.Error _ as e -> e
    | Result.Ok sq -> begin
        match P.rename_new_vars sq ?alt ~base () with
        | Result.Error e -> Result.error (Compute_rename e)
        | Result.Ok sq ->
            let bs = Term.get_bind_state () in
            let schem = !Term.schematic_instantiations in
            Result.ok [(sq, bs, schem)]
      end
  in
  let todo =
    List.fold_left
      (fun acc h ->
        match acc with
        | Result.Error _ as e -> e
        | Result.Ok l -> begin
            match
              P.get_hyp_or_lemma sq (Prover.stmt_name h)
            with
            | Result.Error e ->
                Result.error (Compute_stmt e)
            | Result.Ok form ->
                Result.ok ({ clr = h ; form } :: l)
          end)
      (Result.ok []) hs
    |> Result.map List.rev
  in
  try
    P.map_tactic_failure
      (fun msg -> Compute_tactic_failure msg)
      (fun () ->
        match todo with
        | Result.Error _ as e -> e
        | Result.Ok todo -> begin
            match compute_all sq ~chs:[] ~wait:[] ~todo with
            | Result.Error _ as e -> e
            | Result.Ok triples ->
                Result.ok (P.build_subgoals_full base triples)
          end)
  with Out_of_gas ->
    Result.error (Compute_out_of_gas total_gas)

let compute_all sq ?hint ?gas clr =
  let hs =
    List.map
      (fun (h : P.hyp) ->
        if clr = `CLEAR then Remove (h.P.id, [])
        else Keep (h.P.id, []))
      sq.P.hyps
  in
  compute sq ?hint ?gas hs
