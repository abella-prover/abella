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
open Types
open Unifyty
open Extensions

open Result.Syntax

module Setup = Driver_setup
module P = Prover

(* Owned proof cursor *)

let istate : P.proof_state option ref = State.rref None

(* Suppress the next interactive proof-state display, after
   [Show]/[ShowModule] which print their own output. Mirrors
   [Driver.suppress_proof_state_display]. *)
let suppress_proof_state_display = State.rref false

let get_ist () =
  match !istate with
  | Some st -> st
  | None -> [%bug] "no proof in progress"

let set_ist st = istate := Some st

(* Compute errors at the driver boundary *)

let string_of_compute_error = function
  | Compute.Compute_stmt e -> Prover.string_of_stmt_error e
  | Compute.Compute_rename e ->
      Prover.string_of_rename_hint_error e
  | Compute.Compute_out_of_gas n ->
      Printf.sprintf
        "Compute ran out of gas (given %d) -- looping?" n
  | Compute.Compute_tactic_failure s -> s
let or_fail to_string = function
  | Result.Ok x -> x
  | Result.Error e -> failwith (to_string e)

(* Failures [Try]/[Alt]/[Repeat] recover from: the same exception
   set [Prover] catches, plus [Strict_name] (strict-mode name
   warnings abort tactics like the original's [Failure]). *)
let is_recoverable = function
  | P.Strict_name _ -> true
  | e -> P.tactic_failure_message e <> None

(* Processing errors *)

type type_error = {
  pos : Extensions.pos ;
  actual : Term.ty ;
  expected : Term.ty ;
  kind : Unifyty.constraint_type ;
}

type processing_error =
  | Parse_error of Extensions.pos
  | Syntax_error of Extensions.pos
  | Type_error of type_error
  | Module_parameter_error of {
      parameter : string ;
      ty : Term.ty ;
    }
  | Unification_error of string
  | User_interrupt
  | Runtime_error of string
let pp_type_error ppf { pos ; actual ; expected ; kind } =
  match kind with
  | CArg ->
      Format.fprintf ppf
        "Typing error at %s: expression has type %s but is used \
         here with type %s."
        (Extensions.string_of_position pos)
        (ty_to_string actual) (ty_to_string expected)
  | CFun ->
      Format.fprintf ppf
        "Typing error at %s: expression is applied to too many \
         arguments."
        (Extensions.string_of_position pos)

let pp_parse_error ppf kind pos =
  Format.fprintf ppf "%s at %s."
    kind (Extensions.string_of_position pos)

let pp_module_parameter_error ppf parameter ty =
  Format.fprintf ppf
    "Module parameter %s cannot be instantiated to %s."
    parameter (ty_to_string ty)

let pp_processing_error ppf = function
  | Parse_error pos -> pp_parse_error ppf "Parse error" pos
  | Syntax_error pos -> pp_parse_error ppf "Syntax error" pos
  | Type_error err -> pp_type_error ppf err
  | Module_parameter_error { parameter ; ty } ->
      pp_module_parameter_error ppf parameter ty
  | Unification_error msg -> Format.fprintf ppf "%s" msg
  | User_interrupt ->
      Format.fprintf ppf "Interrupted (use Ctrl-D to quit)"
  | Runtime_error msg -> Format.fprintf ppf "%s" msg

let processing_error_to_string error =
  Format.asprintf "%a" pp_processing_error error

(* Input *)

let interactive_or_exit () =
  if !Setup.mode = `interactive then ()
  else raise @@ Setup.AbellaExit 1

let position_range (p1, p2) =
  let file = p1.Lexing.pos_fname in
  let line = p1.Lexing.pos_lnum in
  let char1 = p1.Lexing.pos_cnum - p1.Lexing.pos_bol in
  let char2 = p2.Lexing.pos_cnum - p1.Lexing.pos_bol in
  if file = "" then
    ""
  else
    Printf.sprintf ": file %s, line %d, characters %d-%d" file line char1 char2

let lexbuf_pos () =
  let lexbuf = !Setup.lexbuf in
  (lexbuf.Lexing.lex_start_p, lexbuf.Lexing.lex_curr_p)
let type_inference_error (pos, ct) exp act =
  Output.msg_printf "Typing error%s." (position_range pos) ;
  match ct with
  | CArg ->
      Output.msg_printf ~severity:Error
        "Expression has type %s but is used here with type %s."
        (ty_to_string act) (ty_to_string exp)
  | CFun ->
      Output.msg_printf ~severity:Error
        "Expression is applied to too many arguments"

let write_compilation () =
  match !Setup.file_kind with
  | `thmod -> Thmod.write_compilation ()
  | `thm -> Thm.write_compilation ()

let is_interactive () = !Setup.mode = `interactive

let bound_params () =
  if Thmod.in_module () then
    Thmod.all_params ()
  else []

let check_thmod_complete () =
  if !Setup.file_kind = `thmod then
    Thmod.check_complete ()

let handle_process_exception e =
  match e with
  | Types.Reported_parse_error ->
      let pos = lexbuf_pos () in
      State.Undo.undo () ;
      Lexing.flush_input !Setup.lexbuf ;
      interactive_or_exit () ;
      Parse_error pos
  | Parser.Error ->
      let pos = lexbuf_pos () in
      State.Undo.undo () ;
      Output.msg_printf ~severity:Error
        "Syntax error%s." (Accumulate.position !Setup.lexbuf) ;
      Lexing.flush_input !Setup.lexbuf ;
      interactive_or_exit () ;
      Syntax_error pos
  | TypeInferenceFailure(exp, act, ci) ->
      let (pos, kind) = ci in
      State.Undo.undo () ;
      type_inference_error ci exp act ;
      interactive_or_exit () ;
      Type_error { pos ; actual = act ; expected = exp ; kind }
  | End_of_file -> raise End_of_file
  | e ->
      State.Undo.undo () ;
      let error = match e with
        | Failure msg -> Runtime_error msg
        | Unify.UnifyFailure fl ->
            Unification_error (Unify.explain_failure fl)
        | Unify.UnifyError (Unify.InstGenericTyvar (v, ty))
          when List.mem v (bound_params ()) ->
            Module_parameter_error { parameter = v ; ty }
        | Unify.UnifyError err ->
            Unification_error (Unify.explain_error err)
        | Unifyty.InstGenericTyvar (v, ty)
          when List.mem v (bound_params ()) ->
            Module_parameter_error { parameter = v ; ty }
        | Unifyty.InstGenericTyvar (v, ty) ->
            Unification_error
              (Unify.explain_error (Unify.InstGenericTyvar (v, ty)))
        | Setup.UserInterrupt -> User_interrupt
        | _ -> Runtime_error (sorry e)
      in
      Output.msg_printf ~severity:Error "Error: %s"
        (processing_error_to_string error) ;
      interactive_or_exit () ;
      error

let resolve_proof_cmd cmd =
  if Thmod.in_module () then
    let is_hyp =
      match !istate with
      | None -> (fun _ -> false)
      | Some st ->
          begin match st.P.focused with
          | None -> (fun _ -> false)
          | Some sq -> Prover.is_hyp sq
          end
    in
    Thmod.resolve_proof_command ~is_hyp cmd
  else
    cmd

(* Queries and flag settings *)

let query q =
  let fv = ids_to_fresh_tyctx (umetaterm_extract_if is_capital_name q) in
  let ctx = fresh_alist ~tag:Logic ~used:[] fv in
  match type_umetaterm ~sr:!sr ~sign:!sign ~ctx (UBinding(Metaterm.Exists, fv, q)) with
  | Binding(Metaterm.Exists, fv, q) ->
      let support = metaterm_support q in
      let ctx = Tactics.fresh_nameless_alist ~sr:!sr ~support ~ts:0 ~tag:Logic fv in
      let q = replace_metaterm_vars ctx q in
      let _ = Tactics.search q
          ~depth:!Prover.search_depth
          ~hyps:[]
          ~clauses:!Prover.clauses
          ~def_unfold:Prover.def_unfold
          ~retype:(fun t -> type_uterm ~sr:!sr ~sign:!sign ~ctx t)
          ~sr:!sr
          ~sc:(fun _w ->
              Output.msg_printf "Found solution:" ;
              List.iter
                (fun (n, v) ->
                   Output.msg_printf "%s = %s" n (term_to_string v))
                ctx ;
              Output.blank_line ())
      in
      Output.msg_printf "No more solutions."
  | _ -> [%bug] "query: expected an existential binding"
let on_or_off = {|"on" or "off"|}

let set_fail ~key ?(expected = on_or_off) v =
  failwithf "Unknown value %S for key %S; expected %s"
    (set_value_to_string v) key expected

let set_subgoal_max_spec spec =
  try
    let buf = Lexing.from_string spec in
    let spec = Parser.depth_spec Lexer.token buf in
    Prover.set_subgoal_max spec
  with
  | Types.Reported_parse_error
  | Parser.Error ->
      failwithf "Invalid subgoal depth specification: %S" spec

let set k v =
  match k, v with
  | "subgoals", Int d when d >= 0 ->
      Prover.reset_subgoal_max () ;
      Prover.set_subgoal_max [d, Some max_int]
  | "subgoals", Str "on" ->
      Prover.reset_subgoal_max () ;
      Prover.set_subgoal_max_default max_int
  | "subgoals", Str "off" ->
      Prover.reset_subgoal_max () ;
      Prover.set_subgoal_max_default 0
  | "subgoals", QStr spec ->
      set_subgoal_max_spec spec
  | "subgoals", _ -> set_fail v
                       ~key:"subgoals"
                       ~expected:{|"on", "off", non-negative integer, or depth specification|}

  | "instantiations", Str "on" -> Prover.show_instantiations := true
  | "instantiations", Str "off" -> Prover.show_instantiations := false
  | "instantiations", _ -> set_fail v
                             ~key:"instantiations"

  | "types", Str "on" -> Metaterm.show_types := true
  | "types", Str "off" -> Metaterm.show_types := false
  | "types", _ -> set_fail v
                    ~key:"types"

  | "search_depth", Int d when d >= 0 -> Prover.search_depth := d
  | "search_depth", _ -> set_fail v
                           ~key:"search_depth"

  | "witnesses", Str "on" -> Setup.witnesses := true
  | "witnesses", Str "off" -> Setup.witnesses := false
  | "witnesses", _ -> set_fail v
                        ~key:"witnesses"

  | "load_path", QStr s ->
      Filepath.set_load_path ~wrt:!Setup.input s
  | _, _ -> failwithf "Unknown key '%s'" k

(* Atomic tactics over the owned proof cursor *)

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
  | Apply (depth, h, args, ws, hint) ->
      let+ gs =
        P.apply sq ?depth ~hint h args ws
          ~term_witness:term_witness
        |> Result.map_error Prover.string_of_apply_error
      in
      Branched gs
  | Backchain (depth, h, ws) ->
      let+ gs =
        P.backchain sq ?depth h ws
          ~term_witness:term_witness
        |> Result.map_error Prover.string_of_backchain_error
      in
      Branched gs
  | Compute (hs, gas, hint) ->
      let+ gs =
        Compute.compute sq ~hint ?gas hs
        |> Result.map_error string_of_compute_error
      in
      Branched gs
  | ComputeAll (gas, hint, clr) ->
      let+ gs =
        Compute.compute_all sq ~hint ?gas clr
        |> Result.map_error string_of_compute_error
      in
      Branched gs
  | Cut (h, arg, hint) ->
      let+ sq' =
        P.cut sq ~hint h arg
        |> Result.map_error Prover.string_of_cut_error
      in
      Updated sq'
  | CutFrom (h, arg, t, hint) ->
      let+ sq' =
        P.cut_from sq ~hint h arg t
        |> Result.map_error Prover.string_of_cut_from_error
      in
      Updated sq'
  | SearchCut (h, hint) ->
      let+ sq' =
        P.search_cut sq ~hint h
        |> Result.map_error Prover.string_of_search_cut_error
      in
      Updated sq'
  | Inst (h, ws, hint) ->
      let+ sq' =
        P.inst sq ~hint h ws
        |> Result.map_error Prover.string_of_inst_error
      in
      Updated sq'
  | Case (str, hint) ->
      let+ gs =
        P.case sq ~hint str
        |> Result.map_error Prover.string_of_case_error
      in
      Branched gs
  | Assert (t, dp, hint) ->
      untyped_ensure_no_restrictions t ;
      let+ delayed =
        P.assert_hyp sq ~hint ?depth:dp t
        |> Result.map_error Prover.string_of_assert_error
      in
      (match delayed with
       | P.Solved sq -> Updated sq
       | P.Delayed gs -> Branched gs)
  | Monotone (h, t, hint) ->
      let+ delayed =
        P.monotone sq ~hint h t
        |> Result.map_error Prover.string_of_monotone_error
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
            |> Result.map_error Prover.string_of_exists_error)
          (Result.ok sq) ews
      in
      Updated sq'
  | Clear (cm, hs) ->
      let+ sq' =
        P.clear sq cm hs
        |> Result.map_error Prover.string_of_clear_error
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
        |> Result.map_error Prover.string_of_rename_error
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
        |> Result.map_error Prover.string_of_search_error
      in
      Branched gs
    end
  | Saturate sat ->
      let+ gs =
        P.saturate sq ~hint:sat.hint ?depth:sat.depth sat.lemmas
        |> Result.map_error Prover.string_of_saturate_error
      in
      Branched gs
  | Permute (ids, h) ->
      let+ sq' =
        P.permute sq ids h
        |> Result.map_error Prover.string_of_permute_error
      in
      Updated sq'
  | Split ->
      let+ gs =
        P.split sq false
        |> Result.map_error Prover.string_of_split_error
      in
      Branched gs
  | SplitStar ->
      let+ gs =
        P.split sq true
        |> Result.map_error Prover.string_of_split_error
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
        |> Result.map_error Prover.string_of_unfold_error
      in
      Branched gs
  | Intros hs ->
      let+ sq' =
        P.intros sq hs
        |> Result.map_error (fun (P.Intros_rename e) ->
            Prover.string_of_rename_hint_error e)
      in
      Updated sq'
  | Skip ->
      istate :=
        Some { (get_ist ()) with P.skip_seen = true } ;
      Result.ok (Branched (P.skip sq))
  | Induction _ | CoInduction _ | Bullet _ | Abort | Undo | Common _
  | Try _ | Then _ | Alt _ | Repeat _ ->
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
  | Alt (t1, t2) ->
      let snap = State.snapshot () in
      begin match eval_tac ~resolve sq t1 with
      | Result.Ok _ as ok -> ok
      | Result.Error _ ->
          State.reload snap ;
          eval_tac ~resolve sq t2
      | exception e when is_recoverable e ->
          State.reload snap ;
          eval_tac ~resolve sq t2
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
          [%bug] "unfocused proof with empty bullet stack"
      | f :: _ ->
          failwith
            (Prover.string_of_bullet_error
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

(* Proof-state display *)

let get_display () =
  match !istate with
  | None -> "@\nNo proof in progress.@\n@\n"
  | Some st -> Prover.get_display st

let state_json () : Json.t =
  match !istate with
  | None -> [%bug] "state_json: no proof in progress"
  | Some st -> Prover.state_json st

(* Proof lifecycle and main loop *)

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
  let resolve = resolve_proof_cmd in
  begin match resolve cmd with
  | Induction (args, hint) ->
      update_focused Prover.string_of_induction_error (fun sq ->
          P.induction sq ~hint args)
  | CoInduction hint ->
      update_focused Prover.string_of_coinduction_error (fun sq ->
          P.coinduction sq ~hint ())
  | Bullet b ->
      set_ist
        (normalize_focused
           (or_fail Prover.string_of_bullet_error
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
  | Common (Set (k, v)) -> set k v
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
      | e -> Error (handle_process_exception e)
    end

(* Top level: proofs are started with [begin_proof], which installs
   an explicit proof state in [istate]. Everything here only
   touches shared global tables, never the current proof state. *)

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
      check_thmod_complete () ;
      write_compilation () ;
      begin match state with
      | Process_top ->
          if not (is_interactive ())
             && !Setup.unfinished <> []
          then begin
            Output.msg_printf
              "There were skips in these theorem(s): %s"
              (String.concat ", " (List.unique !Setup.unfinished))
          end ;
          if not (is_interactive ())
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
      | e -> Error (handle_process_exception e)
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
    | TopCommon (Set (k, v)) -> set k v ; Process_top
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
        begin match mi.source with
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
    | Query q -> query q ; Process_top
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
        compile @@ CType (ids, typarams, ty) ;
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

(* Session snapshot and greeting *)

let initial_snapshot = State.snapshot ()

let () = Setup.initial_snapshot := Some initial_snapshot

let welcome_msg =
  Printf.sprintf "Welcome to Abella %s.\n" Version.version
