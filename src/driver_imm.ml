(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2026 Inria (Institut National de Recherche            *)
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
open Typing
open Metaterm
open Checks
open Abella_types
open Extensions

open Result.Syntax

module Setup = Driver_setup
module P = Prover_imm

(* Owned proof cursor *)

let istate : P.proof_state option ref = State.rref None

(* Suppress the next interactive proof-state display, after
   [Show]/[ShowModule] which print their own output. Mirrors
   [Driver.suppress_proof_state_display]. *)
let suppress_proof_state_display = State.rref false

let get_ist () =
  match !istate with
  | Some st -> st
  | None -> [%bug] "immutable driver: no proof in progress"

let set_ist st = istate := Some st

(* Error printers: bespoke errors become failure strings at
   the driver boundary (surfaced as Runtime_error by
   [Driver.handle_process_exception]). *)

let string_of_stmt_error = function
  | P.Unknown_stmt s ->
      Printf.sprintf "Could not find hypothesis or lemma %s" s
  | P.Extrude_unknown h ->
      Printf.sprintf "Cannot extrude unknown hypothesis %s" h
  | P.Lemma_arity { name ; expected ; got } ->
      Printf.sprintf
        "Lemma %s needs mappings for %d types but got %d"
        name expected got
  | P.Lemma_prop_arg s ->
      Printf.sprintf "Type argument %s may not contain prop" s

let string_of_rename_hint_error = function
  | P.Bad_nominal_hint s ->
      Printf.sprintf
        "Hint %S is not a valid nominal constant name; use n<number>"
        s
  | P.Nominal_in_use s ->
      Printf.sprintf
        "Nominal hint %S is already free in the subgoal" s
  | P.Reserved_nominal_hint s ->
      Printf.sprintf "Hint %S is reserved for nominal constants" s

let string_of_induction_error = function
  | P.Coinductive_goal ->
      "Induction within coinduction is not allowed"
  | P.Arity_mismatch { expected ; got } ->
      Printf.sprintf "Expecting %d induction arguments but got %d"
        expected got
  | P.Not_inductive s -> s
  | P.Bad_induction_target s -> s
  | P.Induction_tactic_failure s -> s

let string_of_coinduction_error = function
  | P.Inductive_inside ->
      "Coinduction within induction is not allowed"
  | P.Not_coinductive s -> s
  | P.Bad_coinduction_target s -> s
  | P.Coinduction_tactic_failure s -> s

let string_of_split_error = function
  | P.Needless_split -> "Needless use of split"

let string_of_exists_error = function
  | P.Not_existential ->
      "Witness can only be given for an existential goal"
  | P.Unresolvable_witness s ->
      Printf.sprintf "Could not resolve existential witness %s" s
  | P.Exists_type_error s -> s

let string_of_clear_error = function
  | P.Unknown_label h ->
      Printf.sprintf "Unknown hypothesis or variable %s" h
  | P.Strict_var_in_use h ->
      Printf.sprintf
        "Cannot clear strict uninstantiated variable %s" h
  | P.Extrude_unknown h ->
      Printf.sprintf "Cannot extrude unknown hypothesis %s" h

let string_of_rename_error = function
  | P.Lemma_clash s ->
      Printf.sprintf "%S already refers to a lemma" s
  | P.Hyp_clash s ->
      Printf.sprintf
        "%S already refers to an existing hypothesis" s
  | P.Var_clash s ->
      Printf.sprintf
        "%S already refers to an existing variable" s
  | P.Unknown_rename_label s ->
      Printf.sprintf "Unknown variable or hypothesis label %S" s

let string_of_permute_error = function
  | P.Not_a_permutation -> "Not a permutation"
  | P.Unknown_permute_hyp h ->
      Printf.sprintf "Unknown hypothesis %s" h
  | P.Permute_tactic_failure s -> s

let string_of_inst_error = function
  | P.Inst_stmt e -> string_of_stmt_error e
  | P.Inst_not_object ->
      "Cannot instantiate this hypothesis\n\
      \ Instantiation can only be used on hypotheses of the form {...}"
  | P.Inst_nominal_not_in_support n ->
      Printf.sprintf "Nominal constant %s not in support" n
  | P.Inst_type_error s -> s
  | P.Inst_tactic_failure s -> s

let string_of_cut_error = function
  | P.Cut_stmt e -> string_of_stmt_error e
  | P.Cut_not_object ->
      "Cut can only be used on hypotheses of the form {...}"
  | P.Cut_tactic_failure s -> s

let string_of_cut_from_error = function
  | P.Cut_from_stmt e -> string_of_stmt_error e
  | P.Cut_from_not_object ->
      "The cut command can only be used on \
       hypotheses of the form {...}"
  | P.Cut_from_type_error s -> s
  | P.Cut_from_tactic_failure s -> s

let string_of_search_cut_error = function
  | P.Search_cut_stmt e -> string_of_stmt_error e
  | P.Search_cut_not_object ->
      "Cut can only be used on hypotheses of the form {... |- ...}"
  | P.Search_cut_tactic_failure s -> s

let string_of_search_error = function
  | P.Search_failed -> "Search failed"
  | P.Search_tactic_failure s -> s

let string_of_apply_error = function
  | P.Apply_stmt e -> string_of_stmt_error e
  | P.Apply_unknown_with_var id ->
      Printf.sprintf "Unknown variable %s" id
  | P.Apply_type_error s -> s
  | P.Apply_restriction s -> s
  | P.Apply_logic_variable ->
      {|Found logic variable at toplevel.
This usually means that the `search` tactic could not fully solve a goal.
Note: the `search` tactic may have been invoked implicitly by `apply`,
`backchain`, etc. with unknown arguments.|}
  | P.Apply_rename e -> string_of_rename_hint_error e
  | P.Apply_tactic_failure s -> s

let string_of_backchain_error = function
  | P.Backchain_stmt e -> string_of_stmt_error e
  | P.Backchain_unknown_with_var id ->
      Printf.sprintf "Unknown variable %s" id
  | P.Backchain_type_error s -> s
  | P.Backchain_logic_variable ->
      {|Found logic variable at toplevel.
This usually means that the `search` tactic could not fully solve a goal.
Note: the `search` tactic may have been invoked implicitly by `apply`,
`backchain`, etc. with unknown arguments.|}
  | P.Backchain_tactic_failure s -> s

let string_of_case_error = function
  | P.Case_stmt e -> string_of_stmt_error e
  | P.Case_undefined_atom ->
      "Cannot perform case-analysis on undefined atom"
  | P.Case_rename e -> string_of_rename_hint_error e
  | P.Case_tactic_failure s -> s

let string_of_assert_error = function
  | P.Assert_type_error s -> s
  | P.Assert_rename e -> string_of_rename_hint_error e

let string_of_monotone_error = function
  | P.Monotone_stmt e -> string_of_stmt_error e
  | P.Monotone_not_object ->
      "The monotone command can only be used on hypotheses \
       of the form {...}"
  | P.Monotone_type_error s -> s
  | P.Monotone_rename e -> string_of_rename_hint_error e
  | P.Monotone_tactic_failure s -> s

let string_of_saturate_error = function
  | P.Unknown_saturate_lemma h ->
      Printf.sprintf "Could not find hypothesis or lemma %s" h
  | P.Saturate_rename e -> string_of_rename_hint_error e
  | P.Saturate_tactic_failure s -> s

let string_of_unfold_error = function
  | P.Unfold_tactic_failure s -> s

let string_of_compute_error = function
  | Compute_imm.Compute_stmt e -> string_of_stmt_error e
  | Compute_imm.Compute_rename e ->
      string_of_rename_hint_error e
  | Compute_imm.Compute_out_of_gas n ->
      Printf.sprintf
        "Compute ran out of gas (given %d) -- looping?" n
  | Compute_imm.Compute_tactic_failure s -> s

let string_of_bullet_error = function
  | P.Bullet_already_active b ->
      Printf.sprintf
        "Bullet %s is already active in an enclosing subgoal" b
  | P.Wrong_bullet { expected ; got } ->
      Printf.sprintf "Wrong bullet %s: expected %s" got expected
  | P.Unfocused_no_bullets ->
      [%bug] "unfocused subgoal with empty bullet stack"
  | P.No_focused_subgoal b ->
      Printf.sprintf
        "No focused subgoal. Use bullet %s to focus the next subgoal"
        b

let or_fail to_string = function
  | Result.Ok x -> x
  | Result.Error e -> failwith (to_string e)

(* Failures [Try]/[Repeat] recover from: the same exception
   set [Prover] catches, plus [Strict_name] (strict-mode name
   warnings abort tactics like the original's [Failure]). *)
let is_recoverable = function
  | P.Strict_name _ -> true
  | e -> P.tactic_failure_message e <> None

(* Atomic tactics *)

let term_witness (_t, w) =
  if !Setup.witnesses then
    Output.msg_printf "Witness: %s." (witness_to_string w)

let handle_search_witness w =
  if !Setup.witnesses then
    Output.msg_printf "Witness: %s." (witness_to_string w)

type outcome =
  | Updated of P.sequent
  | Branched of P.sequent list

let outcome_list = function
  | Updated sq -> [sq]
  | Branched gs -> gs

let run_atomic ~resolve sq cmd
    : (outcome, string) result =
  let cmd = cmd |> Prover.refresh_command_tyvars |> resolve in
  match cmd with
  | Apply (depth, h, args, ws, hn) ->
      let+ gs =
        P.apply sq ?depth ?hint:hn h args ws
          ~term_witness:term_witness
        |> Result.map_error string_of_apply_error
      in
      Branched gs
  | Backchain (depth, h, ws) ->
      let+ gs =
        P.backchain sq ?depth h ws
          ~term_witness:term_witness
        |> Result.map_error string_of_backchain_error
      in
      Branched gs
  | Compute (hs, gas, hn) ->
      let+ gs =
        Compute_imm.compute sq ?hint:hn ?gas hs
        |> Result.map_error string_of_compute_error
      in
      Branched gs
  | ComputeAll (gas, hn, clr) ->
      let+ gs =
        Compute_imm.compute_all sq ?hint:hn ?gas clr
        |> Result.map_error string_of_compute_error
      in
      Branched gs
  | Cut (h, arg, hn) ->
      let+ sq' =
        P.cut sq ?hint:hn h arg
        |> Result.map_error string_of_cut_error
      in
      Updated sq'
  | CutFrom (h, arg, t, hn) ->
      let+ sq' =
        P.cut_from sq ?hint:hn h arg t
        |> Result.map_error string_of_cut_from_error
      in
      Updated sq'
  | SearchCut (h, hn) ->
      let+ sq' =
        P.search_cut sq ?hint:hn h
        |> Result.map_error string_of_search_cut_error
      in
      Updated sq'
  | Inst (h, ws, hn) ->
      let+ sq' =
        P.inst sq ?hint:hn h ws
        |> Result.map_error string_of_inst_error
      in
      Updated sq'
  | Case (str, hn) ->
      let+ gs =
        P.case sq ?hint:hn str
        |> Result.map_error string_of_case_error
      in
      Branched gs
  | Assert (t, dp, hn) ->
      untyped_ensure_no_restrictions t ;
      let+ delayed =
        P.assert_hyp sq ?hint:hn ?depth:dp t
        |> Result.map_error string_of_assert_error
      in
      (match delayed with
       | P.Solved sq -> Updated sq
       | P.Delayed gs -> Branched gs)
  | Monotone (h, t, hn) ->
      let+ delayed =
        P.monotone sq ?hint:hn h t
        |> Result.map_error string_of_monotone_error
      in
      (match delayed with
       | P.Solved sq -> Updated sq
       | P.Delayed gs -> Branched gs)
  | Exists (_, ews) ->
      let+ sq' =
        List.fold_left
          (fun acc ew ->
            let* sq = acc in
            P.exists_tac sq ew
            |> Result.map_error string_of_exists_error)
          (Result.ok sq) ews
      in
      Updated sq'
  | Clear (cm, hs) ->
      let+ sq' =
        P.clear sq cm hs
        |> Result.map_error string_of_clear_error
      in
      Updated sq'
  | ClearDups -> Result.ok (Updated (P.clear_duplicates sq))
  | Abbrev (hs, s) ->
      Result.ok (Updated (P.abbrev sq (Iset.of_list hs) s))
  | Unabbrev hs ->
      Result.ok (Updated (P.unabbrev sq (Iset.of_list hs)))
  | Rename (hfr, hto) ->
      let+ sq' =
        P.rename sq hfr hto
        |> Result.map_error string_of_rename_error
      in
      Updated sq'
  | Search bounds -> begin
      let depth =
        match bounds with
        | `depth n -> Some n
        | _ -> None
      in
      let witness =
        match bounds with
        | `witness w -> w
        | _ -> WMagic
      in
      let+ gs =
        P.search sq ?depth ~witness
          ~handle_witness:handle_search_witness ()
        |> Result.map_error string_of_search_error
      in
      Branched gs
    end
  | Saturate sat ->
      let+ gs =
        P.saturate sq ?hint:sat.hint ?depth:sat.depth sat.lemmas
        |> Result.map_error string_of_saturate_error
      in
      Branched gs
  | Permute (ids, h) ->
      let+ sq' =
        P.permute sq ids h
        |> Result.map_error string_of_permute_error
      in
      Updated sq'
  | Split ->
      let+ gs =
        P.split sq false
        |> Result.map_error string_of_split_error
      in
      Branched gs
  | SplitStar ->
      let+ gs =
        P.split sq true
        |> Result.map_error string_of_split_error
      in
      Branched gs
  | Left ->
      let+ sq' =
        P.left sq
        |> Result.map_error (fun (e : P.disjunction_error) ->
            match e with
            | P.Not_disjunction -> "Goal is not a disjunction")
      in
      Updated sq'
  | Right ->
      let+ sq' =
        P.right sq
        |> Result.map_error (fun (e : P.disjunction_error) ->
            match e with
            | P.Not_disjunction -> "Goal is not a disjunction")
      in
      Updated sq'
  | Unfold (cs, ss) ->
      let+ gs =
        P.unfold sq cs ss
        |> Result.map_error string_of_unfold_error
      in
      Branched gs
  | Intros hs ->
      let+ sq' =
        P.intros sq hs
        |> Result.map_error (fun (P.Intros_rename e) ->
            string_of_rename_hint_error e)
      in
      Updated sq'
  | Skip ->
      istate :=
        Some { (get_ist ()) with P.skip_seen = true } ;
      Result.ok (Branched (P.skip sq))
  | Induction _ | CoInduction _ | Bullet _ | Abort | Undo | Common _
  | Try _ | Then _ | Repeat _ ->
      [%bug] "run_atomic: non-atomic command"

(* Tacticals over explicit sequents *)

let sequent_eq
    (s1 : P.sequent) (s2 : P.sequent) =
  Metaterm.metaterm_eq s1.P.goal s2.P.goal
  && Iset.equal s1.P.user_vars s2.P.user_vars
  && List.length s1.P.vars = List.length s2.P.vars
  && List.for_all2
      (fun (x1, t1) (x2, t2) ->
        x1 = x2 && Term.eq t1 t2)
      s1.P.vars s2.P.vars
  && List.length s1.P.hyps = List.length s2.P.hyps
  && List.for_all2
      (fun
        (h1 : P.hyp)
        (h2 : P.hyp) ->
        h1.P.id = h2.P.id
        && h1.P.abbrev = h2.P.abbrev
        && h1.P.user_named = h2.P.user_named
        && Metaterm.metaterm_eq h1.P.term h2.P.term)
      s1.P.hyps s2.P.hyps

let rec eval_tac ~resolve sq cmd
    : (outcome, string) result =
  match cmd with
  | Then (t1, t2) -> begin
      match eval_tac ~resolve sq t1 with
      | Result.Error _ as e -> e
      | Result.Ok (Updated sq') ->
          eval_tac ~resolve sq' t2
      | Result.Ok (Branched gs) ->
          let rec loop acc = function
            | [] -> Result.ok (Branched (List.concat (List.rev acc)))
            | g :: rest -> begin
                match
                  eval_tac ~resolve
                    (P.activate_sequent g) t2
                with
                | Result.Error _ as e -> e
                | Result.Ok o ->
                    loop (outcome_list o :: acc) rest
              end
          in
          loop [] gs
    end
  | Try t ->
      let snap = State.snapshot () in
      begin match eval_tac ~resolve sq t with
      | Result.Ok _ as ok -> ok
      | Result.Error _ ->
          State.reload snap ;
          Result.ok (Updated sq)
      | exception e when is_recoverable e ->
          State.reload snap ;
          Result.ok (Updated sq)
      end
  | Repeat (limit, t) -> repeat_tac ~resolve sq limit t
  | _ -> run_atomic ~resolve sq cmd

and repeat_tac ~resolve sq limit t
    : (outcome, string) result =
  match limit with
  | Some n when n <= 0 -> Result.ok (Updated sq)
  | _ ->
      let next_limit = Option.map (fun n -> n - 1) limit in
      let snap = State.snapshot () in
      begin match eval_tac ~resolve sq t with
      | Result.Error _ ->
          State.reload snap ;
          Result.ok (Updated sq)
      | exception e when is_recoverable e ->
          State.reload snap ;
          Result.ok (Updated sq)
      | Result.Ok o -> begin
          match outcome_list o with
          | [] -> Result.ok (Branched [])
          | [g] ->
              let g = P.activate_sequent g in
              if sequent_eq sq g then Result.ok o
              else repeat_tac ~resolve g next_limit t
          | gs ->
              repeat_list ~resolve
                (List.map P.activate_sequent gs)
                next_limit t
        end
      end

and repeat_list ~resolve gs limit t
    : (outcome, string) result =
  let rec loop acc = function
    | [] -> Result.ok (Branched (List.concat (List.rev acc)))
    | g :: rest -> begin
        match repeat_tac ~resolve g limit t with
        | Result.Error _ as e -> e
        | Result.Ok o -> loop (outcome_list o :: acc) rest
      end
  in
  loop [] gs

(* Install tactic results in the owned cursor *)

(* Mirror [Prover.next_subgoal]'s trailing [normalize_sequent]:
   the newly focused subgoal is normalized under its own
   bind state (this can rename shadowed binders); pending
   siblings stay raw until they are focused. In-place
   tactics and tactical iteration do not normalize, just
   like the original. *)
let normalize_focused st =
  match st.P.focused with
  | None -> st
  | Some sq ->
      let sq = P.activate_sequent sq in
      { st with P.focused = Some (P.normalize_sequent sq) }

let run_tactic ~resolve cmd =
  let st = get_ist () in
  match st.P.focused with
  | None -> begin
      match st.P.bullets with
      | [] ->
          [%bug]
            "immutable driver: unfocused proof with empty bullet stack"
      | f :: _ ->
          failwith
            (string_of_bullet_error
               (P.No_focused_subgoal f.P.bullet))
    end
  | Some sq ->
      let sq = P.activate_sequent sq in
      let outcome =
        try or_fail (fun s -> s) (eval_tac ~resolve sq cmd)
        with P.Strict_name msg -> failwith msg
      in
      (* [Skip] may have set [skip_seen] on the cursor during
         evaluation; carry it into the installed state. *)
      let st = { st with P.skip_seen = (get_ist ()).P.skip_seen } in
      begin match outcome with
      | Updated sq' ->
          (* In-place: focus is unchanged and, like the
             original, not renormalized. *)
          set_ist { st with P.focused = Some sq' }
      | Branched subs ->
          let st' =
            P.push_subgoals { st with P.focused = Some sq } subs
          in
          (* A closing tactic leaves no focus; advance to the
             next pending subgoal, mirroring
             [Prover.run_tactic]. *)
          let st' =
            match st'.P.focused with
            | Some _ -> st'
            | None -> P.next_subgoal st'
          in
          set_ist (normalize_focused st')
      end

let update_focused to_string f =
  let st = get_ist () in
  match st.P.focused with
  | None -> failwith "No focused subgoal"
  | Some sq ->
      let sq' = or_fail to_string (f (P.activate_sequent sq)) in
      set_ist { st with P.focused = Some sq' }

(* Display *)

(* Display: mirrors [Prover]'s pretty-printing, including
   [show_types]/[show_instantiations] verbosity, abbreviated
   hypothesis groups, and the subgoal-depth display budgets
   ([Set subgoals ...] is honored through [Prover]'s
   table). *)

let separate_strings_imm xs =
  let __max_len = 30 in
  let result = ref [] in
  let emit xs =
    result := String.concat "," (List.rev xs) :: !result
  in
  let rec spin nxs pos = function
    | [] -> emit nxs
    | x :: xs ->
        if pos + String.length x + 1 < __max_len then
          spin (x :: nxs) (pos + String.length x + 1) xs
        else begin
          emit nxs ;
          spin [x] (String.length x) xs
        end
  in
  spin [] 0 xs ;
  List.rev !result

let format_typed_vars_imm ff (ty, xs) =
  let open Format in
  List.iter
    begin fun xs ->
      pp_print_string ff "  " ;
      pp_print_string ff xs ;
      pp_print_string ff " : " ;
      pp_open_box ff 0 ;
      Term.format_ty ff ty ;
      pp_close_box ff () ;
      pp_print_newline ff ()
    end
    (separate_strings_imm xs)

let format_vars_imm fmt (sq : P.sequent) =
  let open Format in
  let eigen_vars, inst_vars =
    List.partition Tactics.is_uninstantiated sq.P.vars
  in
  if eigen_vars <> [] then begin
    pp_print_string fmt "Variables: " ;
    if !Metaterm.show_types then begin
      pp_print_newline fmt () ;
      eigen_vars
      |> List.map (fun (x, xtm) -> (Term.tc [] xtm, x))
      |> List.sort (fun (ty1, _) (ty2, _) -> compare ty1 ty2)
      |> List.collate_assoc
      |> List.iter (format_typed_vars_imm fmt)
    end else begin
      pp_open_hovbox fmt 0 ;
      pp_print_string fmt (fst (List.hd eigen_vars)) ;
      List.iter
        (fun v ->
          pp_print_space fmt () ;
          pp_print_string fmt (fst v))
        (List.tl eigen_vars) ;
      pp_close_box fmt () ;
      pp_print_newline fmt ()
    end
  end ;
  if inst_vars <> [] && !Prover.show_instantiations then
    List.iter
      begin fun (v, vtm) ->
        pp_print_string fmt v ;
        pp_print_string fmt " <-- " ;
        Term.format_term fmt vtm ;
        pp_print_newline fmt ()
      end
      inst_vars

let format_hyp_imm fmt (h : P.hyp) =
  Format.fprintf fmt "%s : " h.P.id ;
  begin match h.P.abbrev with
  | None -> format_metaterm fmt h.P.term
  | Some s -> Format.fprintf fmt "%s" s
  end ;
  Format.pp_force_newline fmt ()

let format_hyps_imm fmt (sq : P.sequent) =
  let am, hyps =
    List.fold_left
      begin fun (am, hs) (h : P.hyp) ->
        match h.P.abbrev with
        | None -> (am, h :: hs)
        | Some ab ->
            let am =
              match Itab.find ab am with
              | hs -> Itab.add ab (h.P.id :: hs) am
              | exception Not_found -> Itab.add ab [h.P.id] am
            in
            (am, hs)
      end
      (Itab.empty, []) sq.P.hyps
  in
  Itab.iter
    begin fun ab hs ->
      Format.fprintf fmt "%s : %s@\n"
        (String.concat "," (List.rev hs)) ab
    end
    am ;
  List.iter (format_hyp_imm fmt) (List.rev hyps)

let format_sequent_imm fmt (sq : P.sequent) =
  Format.pp_open_vbox fmt 0 ;
  format_vars_imm fmt sq ;
  format_hyps_imm fmt sq ;
  Format.fprintf fmt "============================@\n " ;
  format_metaterm fmt sq.P.goal ;
  Format.pp_close_box fmt ()

let format_count_other_subgoals_imm fmt n =
  match n with
  | 0 -> ()
  | 1 -> Format.fprintf fmt "1 other subgoal.@\n@\n"
  | n -> Format.fprintf fmt "%d other subgoals.@\n@\n" n

let format_other_subgoals_imm fmt st =
  let pristine = State.snapshot () in
  let budgets = Hashtbl.create 7 in
  let count = ref 0 in
  List.iter
    begin fun (sq : P.sequent) ->
      sq.P.activate () ;
      let depth = String.count sq.P.name '.' in
      let max_goals =
        match Hashtbl.find_opt budgets depth with
        | Some n -> n
        | None ->
            let n =
              match Prover.subgoal_max_at depth with
              | Some n -> n
              | None -> Prover.subgoal_max_default ()
            in
            Hashtbl.add budgets depth n ;
            n
      in
      if max_goals > 0 then begin
        Hashtbl.replace budgets depth (max_goals - 1) ;
        Format.fprintf fmt "@[<1>Subgoal %s%sis:@\n%a@]@\n@\n"
          sq.P.name
          (if sq.P.name = "" then "" else " ")
          format_metaterm (Metaterm.normalize sq.P.goal)
      end else incr count
    end
    st.P.pending ;
  format_count_other_subgoals_imm fmt !count ;
  State.reload pristine

let get_display () =
  let buf = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer buf in
  begin match !istate with
  | None -> Format.fprintf fmt "@\nNo proof in progress.@\n@\n"
  | Some st -> begin
      Format.pp_open_box fmt 0 ;
      begin match st.P.focused with
      | None -> begin
          match st.P.bullets with
          | [] -> Format.fprintf fmt "@\nProof completed.@\n@\n"
          | f :: _ ->
              Format.fprintf fmt "@\n%s@\n@\n"
                (string_of_bullet_error
                   (P.No_focused_subgoal f.P.bullet))
        end
      | Some sq ->
          if sq.P.name = "" then Format.fprintf fmt "@\n"
          else
            Format.fprintf fmt "Subgoal %s:@\n@\n" sq.P.name ;
          format_sequent_imm fmt sq ;
          Format.fprintf fmt "@\n@\n" ;
          format_other_subgoals_imm fmt st
      end ;
      Format.pp_close_box fmt () ;
      Format.pp_print_flush fmt ()
    end
  end ;
  Buffer.contents buf

(* Annotation state, mirroring [Prover.state_json]. *)

let remaining st =
  List.fold_left
    (fun acc f -> acc + List.length f.P.siblings)
    0 st.P.bullets

let format_unfocused st =
  match st.P.bullets with
  | [] ->
      [%bug] "unfocused proof state with empty bullet stack"
  | f :: _ ->
      let n = remaining st in
      Printf.sprintf
        "Subgoal completed. Focus next subgoal with bullet %s (%d subgoal%s \
         remaining)."
        f.P.bullet n
        (if n = 1 then "" else "s")

let state_json () : Json.t =
  match !istate with
  | None ->
      [%bug] "state_json: no proof in progress"
  | Some st -> begin
      match st.P.focused with
      | None ->
          `Assoc
            [ "more", `Int (remaining st) ;
              "goal", `String "" ;
              "hyps", `List [] ;
              "vars", `List [] ;
              "name", `String "" ;
              "unfocused", `String (format_unfocused st) ]
      | Some sq ->
          let vars =
            List.map
              begin fun (((v, t) as vt) : id * term) ->
                `List
                  [ `String v ;
                    (if Tactics.is_uninstantiated vt then `Null
                     else `String (term_to_string t)) ]
              end
              sq.P.vars
          in
          let hyps =
            List.map
              begin fun (h : P.hyp) ->
                `List
                  [ `String h.P.id ;
                    `String (metaterm_to_string h.P.term) ]
              end
              sq.P.hyps
          in
          let goal = metaterm_to_string sq.P.goal in
          `Assoc
            [ "more", `Int (List.length st.P.pending) ;
              "goal", `String goal ;
              "hyps", `List hyps ;
              "vars", `List vars ;
              "name", `String sq.P.name ]
    end

(* Proof lifecycle *)

type processing_state =
  | Process_top
  | Process_proof of proof_processor

and proof_processor = {
  thm_id : int ;
  thm : string ;
  compile : fin -> unit ;
  reset : unit -> unit ;
}

let processing_state : processing_state ref = State.rref Process_top

let placeholder_goal () =
  termobj (const "placeholder" propty)

let begin_proof ~thm_id ~thm ~compile ~reset goal
    : processing_state =
  let bind = Term.get_bind_state () in
  let schem = !Term.schematic_instantiations in
  let sq =
    P.(theorem (empty_sequent (placeholder_goal ())) goal)
  in
  let init = P.start_proof sq in
  istate := Some init ;
  let proc =
    Process_proof
      {
        thm_id ;
        thm ;
        compile ;
        reset =
          (fun () ->
            Term.set_bind_state bind ;
            Term.schematic_instantiations := schem ;
            istate := Some init ;
            reset ()) ;
      }
  in
  processing_state := proc ;
  proc

let audit () =
  ensure_no_prop_schematic_instantiation () ;
  match !istate with
  | None -> ()
  | Some st ->
      let seqs =
        (match st.P.focused with
         | None -> []
         | Some sq -> [sq])
        @ st.P.pending
      in
      List.iter
        (fun (sq : P.sequent) ->
          ensure_no_prop_equality sq.P.goal ;
          List.iter
            (fun (h : P.hyp) ->
              ensure_no_prop_equality h.P.term)
            sq.P.hyps)
        seqs

let rec process_proof_command proc cmd =
  let resolve = Driver.resolve_proof_cmd in
  begin match resolve cmd with
  | Induction (args, hn) ->
      update_focused string_of_induction_error (fun sq ->
          P.induction sq ?hint:hn args)
  | CoInduction hn ->
      update_focused string_of_coinduction_error (fun sq ->
          P.coinduction sq ?hint:hn ())
  | Bullet b ->
      set_ist
        (normalize_focused
           (or_fail string_of_bullet_error
              (P.bullet (get_ist ()) b)))
  | Abort -> raise (Prover.End_proof `aborted)
  | Undo | Common Back ->
      if !Setup.mode = `interactive then State.Undo.back 2
      else
        failwith
          "Cannot use interactive commands in non-interactive mode"
  | Common Reset ->
      if !Setup.mode = `interactive then State.Undo.reset ()
      else
        failwith
          "Cannot use interactive commands in non-interactive mode"
  | Common (Set (k, v)) -> Driver.set k v
  | Common (Show nm) ->
      Output.msg_format "%t" (Prover.show nm) ;
      if !Setup.mode = `interactive then Output.blank_line () ;
      suppress_proof_state_display := true
  | Common (ShowModule src) ->
      Thmod.show_module ~load:load_thmod_artifact src ;
      if !Setup.mode = `interactive then Output.blank_line () ;
      suppress_proof_state_display := true
  | Common Quit -> raise End_of_file
  | _ -> run_tactic ~resolve cmd
  end ;
  audit () ;
  let st = get_ist () in
  if P.is_completed st then begin
    let fin = if st.P.skip_seen then Unfinished else Finished in
    raise (Prover.End_proof (`completed fin))
  end ;
  ignore proc

and process_proof1_body proc =
  if !Setup.mode = `interactive
     && not !suppress_proof_state_display
  then
    Output.non_annot "%s" @@ get_display () ;
  suppress_proof_state_display := false ;
  if !Setup.mode = `interactive then
    Output.non_annot "%s < " proc.thm ;
  let input = Parser.command_start Lexer.token !Setup.lexbuf in
  let cmd_string = command_to_string input.el in
  if !Setup.mode <> `interactive then
    begin match input.el with
    | Bullet _ -> Output.non_annot "%s\n" cmd_string
    | _ -> Output.non_annot "%s.\n" cmd_string
    end ;
  let annot =
    if not !Setup.annotate then None
    else
      (Output.message "proof_command"
         ~fields:
           begin
             [ "thm_id", `Int proc.thm_id ;
               "theorem", `String proc.thm ;
               "start_state", state_json () ;
               "command", `String cmd_string ;
             ]
             @ (if fst input.pos = Lexing.dummy_pos then []
                else ["range", json_of_position input.pos])
           end
       |> Option.some)
  in
  if not !Setup.annotate then process_proof_command proc input.el
  else
    match process_proof_command proc input.el with
    | () ->
        Option.iter
          begin fun annot ->
            Output.extend annot "end_state" @@ state_json ()
            |> Output.commit_message
          end
          annot
    | exception e ->
        Option.iter Output.commit_message annot ;
        raise e

and process_proof1 state =
  match state with
  | Process_top ->
      [%bug] "process_proof1 called in top-level state"
  | Process_proof proc -> begin
      try
        process_proof1_body proc ;
        Ok !processing_state
      with
      | Prover.End_proof reason -> begin
          Output.msg_printf "Proof %s" begin
            match reason with
            | `completed fin -> begin
                proc.compile fin ;
                if fin = Unfinished then
                  Setup.unfinished :=
                    proc.thm :: !Setup.unfinished ;
                Printf.sprintf "completed%s"
                  (match fin with
                   | Finished | Axiomatic -> ""
                   | Unfinished -> " *** USING skip ***")
              end
            | `aborted -> "ABORTED"
          end ;
          proc.reset () ;
          processing_state := Process_top ;
          Ok Process_top
        end
      | e -> Error (Driver.handle_process_exception e)
    end

(* Top level: mirrors [Driver.process_top1_body] but
   starts proofs with [begin_proof]. Everything here only
   touches shared global tables, never the immutable
   sequent, so the bodies are unchanged apart from the
   [Theorem] case and the loaders below. *)

and compile citem =
  if !Setup.file_kind = `thmod || Thmod.in_module () then
    Thmod.add_compiled citem
  else
    Thm.comp_content := citem :: !Thm.comp_content

and record_imported citem =
  if !Setup.file_kind = `thmod || Thmod.in_module () then
    Thmod.add_imported_compiled citem
  else
    Thm.comp_content := citem :: !Thm.comp_content

and bound_params () =
  if Thmod.in_module () then Thmod.all_params () else []

and process1 state =
  processing_state := state ;
  State.Undo.push () ;
  try
    let result =
      match state with
      | Process_top -> process_top1 state
      | Process_proof _ -> process_proof1 state
    in
    begin match result with
    | Ok next -> processing_state := next
    | Error _ -> ()
    end ;
    result
  with
  | End_of_file ->
      Driver.check_thmod_complete () ;
      Driver.write_compilation () ;
      begin match state with
      | Process_top ->
          if not (Driver.is_interactive ())
             && !Setup.unfinished <> []
          then begin
            Output.msg_printf
              "There were skips in these theorem(s): %s"
              (String.concat ", " (List.unique !Setup.unfinished))
          end ;
          if not (Driver.is_interactive ())
             && !Setup.axioms <> []
          then begin
            Output.msg_printf "The following axioms were used: %s"
              (String.concat ", "
                 (List.unique (List.rev !Setup.axioms)))
          end ;
          Output.flush () ;
          raise @@ Setup.AbellaExit 0
      | _ ->
          Output.msg_printf ~severity:Error "Proof NOT Completed." ;
          Output.flush () ;
          raise @@ Setup.AbellaExit 1
      end

and process_top1 state =
  match state with
  | Process_proof _ ->
      [%bug] "process_top1 called in proof state"
  | Process_top -> begin
      try
        let next = process_top1_body () in
        ensure_no_prop_schematic_instantiation () ;
        Ok next
      with
      | e -> Error (Driver.handle_process_exception e)
    end

and process_top1_body () =
  if !Setup.mode = `interactive then Output.non_annot "Abella < " ;
  let input = Parser.top_command_start Lexer.token !Setup.lexbuf in
  let cmd_string = top_command_to_string input.el in
  let input =
    if Thmod.in_module () then
      { input with el = Thmod.resolve_top input.el }
    else input
  in
  if !Setup.mode <> `interactive then
    Output.non_annot "%s.\n%!" cmd_string ;
  Thmod.check_structure input.el ;
  let thm_id =
    if not !Setup.annotate then -1
    else
      let annot =
        Output.message "top_command"
          ~fields:
            ((if fst input.pos = Lexing.dummy_pos then []
              else ["range", json_of_position input.pos])
             @ ["command", `String cmd_string])
      in
      Output.commit_message annot ;
      annot.id
  in
  let next_state =
    begin match input.el with
    | Theorem (name, tys, thm) -> begin
        let thm = type_umetaterm ~sr:!sr ~sign:!sign thm in
        check_theorem ~bound:(bound_params ()) tys thm ;
        let oldsign = !sign in
        let thm_compile fin =
          sign := oldsign ;
          compile (CTheorem (name, tys, thm, fin)) ;
          Artifact.add_lemma ~fin name tys thm
        in
        let thm_reset () = sign := oldsign in
        let next =
          begin_proof ~thm_id ~thm:name ~compile:thm_compile
            ~reset:thm_reset thm
        in
        if !Setup.annotate then
          Output.commit_message
            begin
              Output.message "theorem_state"
                ~fields:
                  [ "thm_id", `Int thm_id ;
                    "theorem", `String name ;
                    "state", state_json () ]
            end ;
        next
      end
    | Axiom (name, tys, thm) ->
        let thm = type_umetaterm ~sr:!sr ~sign:!sign thm in
        check_theorem ~bound:(bound_params ()) tys thm ;
        compile (CTheorem (name, tys, thm, Axiomatic)) ;
        Artifact.add_lemma ~fin:Axiomatic name tys thm ;
        Setup.axioms := name :: !Setup.axioms ;
        Process_top
    | SSplit (name, names) ->
        let fin = Prover.get_lemma_tag name in
        let gen_thms =
          Prover.create_split_theorems name names
          |> List.map (fun (n, t) ->
              if Thmod.in_module () then (Thmod.new_name n, t)
              else (n, t))
        in
        List.iter
          begin fun (n, (tys, t)) ->
            Output.msg_format "%t" (Prover.print_theorem n (tys, t)) ;
            Artifact.add_lemma ~fin n tys t ;
            compile (CTheorem (n, tys, t, fin))
          end
          gen_thms ;
        if fin = Unfinished && List.mem name !Setup.unfinished then
          Setup.unfinished :=
            List.map fst gen_thms @ !Setup.unfinished ;
        if fin = Axiomatic && not (List.mem name !Setup.axioms) then
          Setup.axioms :=
            name :: List.map fst gen_thms @ !Setup.axioms ;
        Process_top
    | Define _ ->
        let strat_errors =
          Thmod.in_module ()
          || !stratification_warnings_are_errors
        in
        compile
          (Prover.register_definition ~strat_errors
             ~bound_tyvars:(bound_params ()) input.el) ;
        Process_top
    | Suspend (head, test) ->
        let g = Compute.make_guard ~head ~test in
        Compute.add_guard g ;
        compile @@ CSuspend g ;
        Process_top
    | TopCommon Back ->
        (if !Setup.mode = `interactive then State.Undo.back 2
         else
           failwith
             "Cannot use interactive commands in non-interactive mode") ;
        !processing_state
    | TopCommon Reset ->
        (if !Setup.mode = `interactive then State.Undo.reset ()
         else
           failwith
             "Cannot use interactive commands in non-interactive mode") ;
        Process_top
    | TopCommon (Set (k, v)) -> Driver.set k v ; Process_top
    | TopCommon (Show n) ->
        Output.msg_format "%t" (Prover.show n) ;
        Process_top
    | TopCommon (ShowModule src) ->
        Thmod.show_module ~load:load_thmod_artifact src ;
        Process_top
    | TopCommon Quit -> raise End_of_file
    | Import (filename, pos, withs) ->
        compile (CImport (filename, withs)) ;
        Thm.import ~load:load_thm_artifact ~wrt:!Setup.input
          pos filename withs ;
        Process_top
    | Module (name, params) ->
        Thmod.process_module name params ;
        Process_top
    | End name ->
        Thmod.process_end name ;
        Process_top
    | ImportModule mi -> begin
        begin match mi.mi_source with
        | QuoteSource (file, pos) ->
            if !Setup.annotate then begin
              let file =
                Filepath.normalize ~wrt:!Setup.input file
              in
              Output.link_message ~pos ~url:(file ^ ".html")
            end
        | NameSource _ -> ()
        end ;
        Thmod.import_module ~load:load_thmod_artifact
          ~record:record_imported mi ;
        Process_top
      end
    | Specification (filename, pos) ->
        (if !Thm.can_read_specification then begin
           let filename =
             Filepath.normalize ~wrt:!Setup.input filename
           in
           Thm.read_specification filename ;
           Thm.ensure_finalized_specification () ;
           if !Setup.annotate then
             Output.link_message ~pos ~url:(filename ^ ".lp.html")
         end
         else
           failwith
             "Specification can only be read \
              at the begining of a development.") ;
        Process_top
    | Query q -> Driver.query q ; Process_top
    | Kind (ids, knd) ->
        Prover.add_global_types ids knd ;
        compile (CKind (ids, knd)) ;
        Process_top
    | Type (ids, ty) ->
        let is_declared_predicate =
          match observe_ty ty with
          | Ty (_, aty) -> aty = propaty
        in
        let typarams =
          if Thmod.in_module () && is_declared_predicate
             && contains_prop_argument ty
          then begin
            let name =
              match ids with
              | id :: _ -> id
              | [] -> "<unknown>"
            in
            failwithf
              "Declared predicate %s may not take an argument containing \
               prop"
              name
          end
          else List.minus (get_typaram ty) (bound_params ())
        in
        Prover.add_global_consts ~typarams
          (List.map (fun id -> (id, ty)) ids) ;
        let comp =
          if Thmod.in_module () && is_declared_predicate then
            CDeclPred (ids, typarams, ty)
          else CType (ids, typarams, ty)
        in
        compile comp ;
        Process_top
    | Close atys ->
        Prover.close_types !sign !Prover.clauses atys ;
        compile
          (CClose
             (List.map
                (fun aty ->
                  (aty, Subordination.subordinates !sr aty))
                atys)) ;
        Process_top
    end
  in
  if not !Setup.annotate then Output.blank_line () ;
  next_state

and load_thm_artifact ~modname =
  Thm.Codec.load ~process:process1 ~init:Process_top ~modname

and load_thmod_artifact ~modname =
  Thmod.Codec.load ~process:process1 ~init:Process_top ~modname
