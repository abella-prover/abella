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

(* Owned proof cursor *)

let istate : Prover.proof_state option ref = State.rref None

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
  | Prover.Strict_name _ -> true
  | e -> Prover.tactic_failure_message e <> None

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
  else begin
    Output.flush () ;
    raise @@ Setup.AbellaExit 1
  end

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
  (* Skipped runs admit theorems without checking them, so they must
     not produce a trusted artifact. Recursive imports reset
     [skip_to] and still compile normally. *)
  if !Setup.skip_to <> None then begin
    match !Setup.compiled with
    | None -> ()
    | Some (module C) ->
        (try Sys.remove C.thc_path with Sys_error _ -> ())
  end else
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
          begin match st.Prover.focused with
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
  let fv_opt = List.map (fun (id, ty) -> (id, Some ty)) fv in
  match type_umetaterm ~sr:!sr ~sign:!sign ~ctx (UBinding(Metaterm.Exists, fv_opt, q)) with
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

type outcome = {
  next : continuation ;
  progressed : bool ; (* did the tactic make progress? *)
}

and continuation =
  | Updated of Prover.sequent
  | Branched of Prover.sequent list

let continuation_list = function
  | Updated sq -> [sq]
  | Branched gs -> gs

let outcome_list o = continuation_list o.next

(* Called by [eval_tac] for non-tactical commands. *)
(* Runs one atomic tactic on an explicit sequent. *)
let run_atomic ~resolve sq cmd
    : (outcome, string) result =
  let cmd = cmd |> resolve in
  match cmd with
  | Apply (depth, h, args, ws, hint) ->
      let+ gs =
        Prover.apply sq ?depth ~hint h args ws
          ~term_witness:term_witness
        |> Result.map_error Prover.string_of_apply_error
      in
      { next = Branched gs ; progressed = true }
  | Backchain (depth, h, ws) ->
      let+ gs =
        Prover.backchain sq ?depth h ws
          ~term_witness:term_witness
        |> Result.map_error Prover.string_of_backchain_error
      in
      { next = Branched gs ; progressed = true }
  | Compute (hs, gas, hint) ->
      let+ gs =
        Compute.compute sq ~hint ?gas hs
        |> Result.map_error string_of_compute_error
      in
      { next = Branched gs ; progressed = true }
  | ComputeAll (gas, hint, clr) ->
      let+ gs =
        Compute.compute_all sq ~hint ?gas clr
        |> Result.map_error string_of_compute_error
      in
      { next = Branched gs ; progressed = true }
  | Cut (h, arg, hint) ->
      let+ sq =
        Prover.cut sq ~hint h arg
        |> Result.map_error Prover.string_of_cut_error
      in
      { next = Updated sq ; progressed = true }
  | CutFrom (h, arg, t, hint) ->
      let+ sq =
        Prover.cut_from sq ~hint h arg t
        |> Result.map_error Prover.string_of_cut_from_error
      in
      { next = Updated sq ; progressed = true }
  | SearchCut (h, hint) ->
      let+ sq =
        Prover.search_cut sq ~hint h
        |> Result.map_error Prover.string_of_search_cut_error
      in
      { next = Updated sq ; progressed = true }
  | Inst (h, ws, hint) ->
      let+ sq =
        Prover.inst sq ~hint h ws
        |> Result.map_error Prover.string_of_inst_error
      in
      { next = Updated sq ; progressed = true }
  | Case (str, hint) ->
      let+ gs =
        Prover.case sq ~hint str
        |> Result.map_error Prover.string_of_case_error
      in
      { next = Branched gs ; progressed = true }
  | Assert (t, dp, hint) ->
      untyped_ensure_no_restrictions t ;
      let+ delayed =
        Prover.assert_hyp sq ~hint ?depth:dp t
        |> Result.map_error Prover.string_of_assert_error
      in
      (match delayed with
       | Prover.Solved sq -> { next = Updated sq ; progressed = true }
       | Prover.Delayed gs -> { next = Branched gs ; progressed = true })
  | Monotone (h, t, hint) ->
      let+ delayed =
        Prover.monotone sq ~hint h t
        |> Result.map_error Prover.string_of_monotone_error
      in
      (match delayed with
       | Prover.Solved sq -> { next = Updated sq ; progressed = true }
       | Prover.Delayed gs -> { next = Branched gs ; progressed = true })
  | Exists (_, ews) ->
      let+ sq =
        List.fold_left
          (fun acc ew ->
            let* sq = acc in
            Prover.exists_tac sq ew
            |> Result.map_error Prover.string_of_exists_error)
          (Result.ok sq) ews
      in
      { next = Updated sq ; progressed = (ews <> []) }
  | Clear (cm, hs) ->
      let+ sq =
        Prover.clear sq cm hs
        |> Result.map_error Prover.string_of_clear_error
      in
      { next = Updated sq ; progressed = (hs <> []) }
  | ClearDups ->
      let len = List.length sq.Prover.hyps in
      let sq = Prover.clear_duplicates sq in
      let progressed = List.length sq.Prover.hyps <> len in
      Result.ok { next = Updated sq ; progressed }
  | Abbrev (hs, s) ->
      let ids = Iset.of_list hs in
      let progressed =
        List.exists
          (fun (h : Prover.hyp) ->
            Iset.mem h.Prover.id ids && h.Prover.abbrev <> Some s)
          sq.Prover.hyps
      in
      Result.ok
        { next = Updated (Prover.abbrev sq ids s) ; progressed }
  | Unabbrev hs ->
      let ids = Iset.of_list hs in
      let progressed =
        List.exists
          (fun (h : Prover.hyp) ->
            Iset.mem h.Prover.id ids && h.Prover.abbrev <> None)
          sq.Prover.hyps
      in
      Result.ok
        { next = Updated (Prover.unabbrev sq ids) ; progressed }
  | Rename (hfr, hto) ->
      let+ sq =
        Prover.rename sq hfr hto
        |> Result.map_error Prover.string_of_rename_error
      in
      { next = Updated sq ; progressed = (hfr <> hto) }
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
        Prover.search sq ?depth ~witness
          ~handle_witness:handle_search_witness ()
        |> Result.map_error Prover.string_of_search_error
      in
      { next = Branched gs ; progressed = true }
    end
  | Saturate sat ->
      let+ gs =
        Prover.saturate sq ~hint:sat.hint ?depth:sat.depth sat.lemmas
        |> Result.map_error Prover.string_of_saturate_error
      in
      let progressed =
        List.exists
          (fun (g : Prover.sequent) ->
            List.length g.Prover.hyps > List.length sq.Prover.hyps)
          gs
      in
      { next = Branched gs ; progressed }
  | Permute (ids, h) ->
      let+ sq =
        Prover.permute sq ids h
        |> Result.map_error Prover.string_of_permute_error
      in
      { next = Updated sq ; progressed = (ids <> [] || h <> None) }
  | Split ->
      let+ gs =
        Prover.split sq false
        |> Result.map_error Prover.string_of_split_error
      in
      { next = Branched gs ; progressed = true }
  | SplitStar ->
      let+ gs =
        Prover.split sq true
        |> Result.map_error Prover.string_of_split_error
      in
      { next = Branched gs ; progressed = true }
  | Left ->
      let progressed =
        match sq.Prover.goal with
        | Or _ -> true
        | _ -> false
      in
      let+ sq =
        Prover.left sq
        |> Result.map_error (fun (e : Prover.disjunction_error) ->
            match e with
            | Prover.Not_disjunction -> "Goal is not a disjunction")
      in
      { next = Updated sq ; progressed }
  | Right ->
      let progressed =
        match sq.Prover.goal with
        | Or _ -> true
        | _ -> false
      in
      let+ sq =
        Prover.right sq
        |> Result.map_error (fun (e : Prover.disjunction_error) ->
            match e with
            | Prover.Not_disjunction -> "Goal is not a disjunction")
      in
      { next = Updated sq ; progressed }
  | Unfold (cs, ss) ->
      let+ gs =
        Prover.unfold sq cs ss
        |> Result.map_error Prover.string_of_unfold_error
      in
      { next = Branched gs ; progressed = true }
  | Intros hs ->
      let progressed =
        match sq.Prover.goal with
        | Arrow _ -> true
        | Binding (Forall, _, _) -> true
        | Binding (Nabla, _, _) -> true
        | _ -> false
      in
      let+ sq =
        Prover.intros sq hs
        |> Result.map_error (fun (Prover.Intros_rename e) ->
            Prover.string_of_rename_hint_error e)
      in
      { next = Updated sq ; progressed }
  | Skip ->
      istate :=
        Some { (get_ist ()) with Prover.skip_seen = true } ;
      Result.ok { next = Branched (Prover.skip sq) ; progressed = true }
  | Induction _ | CoInduction _ | Bullet _ | Abort | Undo | Common _
  | Try _ | Then _ | Alt _ | Repeat _ ->
      [%bug] "run_atomic: non-atomic command"

(* Tacticals over explicit sequents *)

let rec eval_tac ~resolve sq cmd
    : (outcome, string) result =
  match cmd with
  | Then (t1, t2) -> begin
      match eval_tac ~resolve sq t1 with
      | Result.Error _ as e -> e
      | Result.Ok { next = Updated sq ; progressed = p1 } -> begin
          match eval_tac ~resolve sq t2 with
          | Result.Error _ as e -> e
          | Result.Ok { next ; progressed = p2 } ->
              Result.ok { next ; progressed = (p1 || p2) }
        end
      | Result.Ok { next = Branched gs ; progressed = p1 } ->
          let rec loop acc prog = function
            | [] ->
                let p2 =
                  match gs with
                  | [] -> true
                  | _ -> prog
                in
                Result.ok
                  { next = Branched (List.concat (List.rev acc))
                  ; progressed = (p1 || p2) }
            | g :: rest -> begin
                match
                  eval_tac ~resolve
                    (Prover.activate_sequent g) t2
                with
                | Result.Error _ as e -> e
                | Result.Ok o ->
                    loop (outcome_list o :: acc) (prog || o.progressed)
                      rest
              end
          in
          loop [] false gs
    end
  | Try t ->
      let snap = State.snapshot () in
      begin match eval_tac ~resolve sq t with
      | Result.Ok _ as ok -> ok
      | Result.Error _ ->
          State.reload snap ;
          Result.ok { next = Updated sq ; progressed = false }
      | exception e when is_recoverable e ->
          State.reload snap ;
          Result.ok { next = Updated sq ; progressed = false }
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

and repeat_tac ~resolve ?(progressed = false) sq limit t
    : (outcome, string) result =
  match limit with
  | Some n when n <= 0 -> Result.ok { next = Updated sq ; progressed }
  | _ ->
      let next_limit = Option.map (fun n -> n - 1) limit in
      let snap = State.snapshot () in
      begin match eval_tac ~resolve sq t with
      | Result.Error _ ->
          State.reload snap ;
          Result.ok { next = Updated sq ; progressed }
      | exception e when is_recoverable e ->
          State.reload snap ;
          Result.ok { next = Updated sq ; progressed }
      | Result.Ok o -> begin
          if not o.progressed then
            Result.ok { next = o.next ; progressed }
          else
            let progressed = true in
            match outcome_list o with
            | [] -> Result.ok { next = Branched [] ; progressed }
            | [g] ->
                repeat_tac ~resolve ~progressed
                  (Prover.activate_sequent g) next_limit t
            | gs ->
                begin match
                  repeat_list ~resolve
                    (List.map Prover.activate_sequent gs)
                    next_limit t
                with
                | Result.Error _ as e -> e
                | Result.Ok { next ; progressed = p } ->
                    Result.ok
                      { next ; progressed = (progressed || p) }
                end
        end
      end

and repeat_list ~resolve gs limit t
    : (outcome, string) result =
  let rec loop acc prog = function
    | [] ->
        Result.ok
          { next = Branched (List.concat (List.rev acc))
          ; progressed = prog }
    | g :: rest -> begin
        match repeat_tac ~resolve g limit t with
        | Result.Error _ as e -> e
        | Result.Ok o ->
            loop (outcome_list o :: acc) (prog || o.progressed) rest
      end
  in
  loop [] false gs

(* Install tactic results in the owned cursor *)

(* Mirror [Prover.next_subgoal]'s trailing [normalize_sequent]:
   the newly focused subgoal is normalized under its own
   bind state (this can rename shadowed binders); pending
   siblings stay raw until they are focused. In-place
   tactics and tactical iteration do not normalize, just
   like the original. *)
let normalize_focused st =
  match st.Prover.focused with
  | None -> st
  | Some sq ->
      let sq = Prover.activate_sequent sq in
      { st with Prover.focused = Some (Prover.normalize_sequent sq) }

(* Called by [process_proof_command] on the owned cursor. *)
(* Evaluates tacticals and installs the resulting subgoals. *)
let run_tactic ~resolve cmd =
  let st = get_ist () in
  match st.Prover.focused with
  | None -> begin
      match st.Prover.bullets with
      | [] ->
          [%bug] "unfocused proof with empty bullet stack"
      | f :: _ ->
          failwith
            (Prover.string_of_bullet_error
               (Prover.No_focused_subgoal f.Prover.bullet))
    end
  | Some sq ->
      let sq = Prover.activate_sequent sq in
      let outcome =
        try or_fail (fun s -> s) (eval_tac ~resolve sq cmd)
        with Prover.Strict_name msg -> failwith msg
      in
      (* [Skip] may have set [skip_seen] on the cursor during
         evaluation; carry it into the installed state. *)
      let st = { st with Prover.skip_seen = (get_ist ()).Prover.skip_seen } in
      begin match outcome.next with
      | Updated sq ->
          (* In-place: focus is unchanged and, like the
             original, not renormalized. *)
          set_ist { st with Prover.focused = Some sq }
      | Branched subs ->
          let st =
            Prover.push_subgoals { st with Prover.focused = Some sq } subs
          in
          (* A closing tactic leaves no focus; advance to the
             next pending subgoal, mirroring
             [Prover.run_tactic]. *)
          let st =
            match st.Prover.focused with
            | Some _ -> st
            | None -> Prover.next_subgoal st
          in
          set_ist (normalize_focused st)
      end

let update_focused to_string f =
  let st = get_ist () in
  match st.Prover.focused with
  | None -> failwith "No focused subgoal"
  | Some sq ->
      let sq = or_fail to_string (f (Prover.activate_sequent sq)) in
      set_ist { st with Prover.focused = Some sq }

(* Proof-state display *)

let get_display () =
  match !istate with
  | None -> "@\nNo proof in progress.@\n@\n"
  | Some st -> Prover.get_display st

let maybe_print_interactions () =
  if !Setup.print_interactions && !Setup.mode = `batch then
    Output.non_annot "%s" @@ get_display ()

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
    Prover.(theorem (empty_sequent (placeholder_goal ())) goal)
  in
  let init = Prover.start_proof sq in
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
        (match st.Prover.focused with
         | None -> []
         | Some sq -> [sq])
        @ st.Prover.pending
      in
      List.iter
        (fun (sq : Prover.sequent) ->
          ensure_no_prop_equality sq.Prover.goal ;
          List.iter
            (fun (h : Prover.hyp) ->
              ensure_no_prop_equality h.Prover.term)
            sq.Prover.hyps)
        seqs

(* Called by [process_proof1_body] for each proof command. *)
(* Dispatches built-ins or runs tactics; raises [End_proof]. *)
let rec process_proof_command proc cmd =
  let resolve = resolve_proof_cmd in
  begin match resolve cmd with
  | Induction (args, hint) ->
      update_focused Prover.string_of_induction_error (fun sq ->
          Prover.induction sq ~hint args)
  | CoInduction hint ->
      update_focused Prover.string_of_coinduction_error (fun sq ->
          Prover.coinduction sq ~hint ())
  | Bullet b ->
      set_ist
        (normalize_focused
           (or_fail Prover.string_of_bullet_error
              (Prover.bullet (get_ist ()) b)))
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
  if Prover.is_completed st then begin
    let fin = if st.Prover.skip_seen then Unfinished else Finished in
    raise (Prover.End_proof (`completed fin))
  end ;
  ignore proc

(* Called by [process_proof1] for a single proof step. *)
(* Parses, echoes, and executes the next proof command. *)
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
  if not !Setup.annotate then begin
    process_proof_command proc input.el ;
    maybe_print_interactions ()
  end else
    match process_proof_command proc input.el with
    | () ->
        maybe_print_interactions () ;
        Option.iter
          begin fun annot ->
            Output.extend annot "end_state" @@ state_json ()
            |> Output.commit_message
          end
          annot
    | exception e ->
        Option.iter Output.commit_message annot ;
        raise e

(* Called by [process1] while inside a proof. *)
(* Catches [End_proof]/errors and returns the next state. *)
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

(* Called by the main loop and by artifact loading. *)
(* Dispatches top/proof steps and handles [End_of_file]. *)
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
      begin match !Setup.skip_to with
      | Some (Setup.Skip_theorem name)
          when not !Setup.skip_reached && not (is_interactive ()) ->
          Output.msg_printf ~severity:Error
            "Error: theorem %S not found (--skip target)" name ;
          Output.flush () ;
          raise @@ Setup.AbellaExit 1
      | _ -> ()
      end ;
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

(* Called by [process1] in top-level state. *)
(* Runs [process_top1_body] and normalizes exceptions. *)
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

(* Called by [process_top1_body] when skipping is off. *)
(* Parses one top command and delegates to [run_top_command]. *)
and process_top1_body_normal () =
  if !Setup.mode = `interactive then Output.non_annot "Abella < " ;
  let input = Parser.top_command_start Lexer.token !Setup.lexbuf in
  let cmd_string = top_command_to_string input.el in
  run_top_command input.el input.pos cmd_string

(* Called by [run_top_command] once setup is done. *)
(* Executes the top-command match; single copy of it. *)
and exec_resolved_top input thm_id =
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
          Output.message "theorem_state"
            ~fields:
              [ "thm_id", `Int thm_id ;
                "theorem", `String name ;
                "state", state_json () ]
          |> Output.commit_message ;
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
        let strat_errors = Thmod.in_module ()
                           || !stratification_warnings_are_errors in
        Prover.register_definition ~strat_errors
          ~bound_tyvars:(bound_params ()) input.el
        |> compile ;
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
        let () = match mi.source with
          | QuoteSource (file, pos) ->
              if !Setup.annotate then
                let file = Filepath.normalize ~wrt:!Setup.input file in
                Output.link_message ~pos ~url:(file ^ ".html")
          | NameSource _ -> () in
        Thmod.import_module ~load:load_thmod_artifact
          ~record:record_imported mi ;
        Process_top
      end
    | Specification (filename, pos) -> begin
        if !Thm.can_read_specification then begin
          let filename = Filepath.normalize ~wrt:!Setup.input filename in
          Thm.read_specification filename ;
          Thm.ensure_finalized_specification () ;
          if !Setup.annotate then
            Output.link_message ~pos ~url:(filename ^ ".lp.html")
        end else
          failwith
            "Specification can only be read \
             at the begining of a development." ;
        Process_top
      end
    | Query q -> query q ; Process_top
    | Kind (ids, knd) ->
        Prover.add_global_types ids knd ;
        compile (CKind (ids, knd)) ;
        Process_top
    | Type (ids, ty) ->
        let is_declared_predicate =
          match observe_ty ty with Ty (_, aty) -> aty = propaty
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

(* Called by normal and skip paths with a parsed command. *)
(* Resolves, echoes, annotates, then calls [exec_resolved_top]. *)
and run_top_command tc pos cmd_string =
  let input =
    if Thmod.in_module () then
      { el = Thmod.resolve_top tc ; pos }
    else
      { el = tc ; pos }
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
  exec_resolved_top input thm_id

and admit_theorem tc pos cmd_string =
  let tc =
    if Thmod.in_module () then Thmod.resolve_top tc else tc
  in
  let input = { el = tc ; pos } in
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
  begin match input.el with
  | Theorem (name, tys, thm) ->
      let thm = type_umetaterm ~sr:!sr ~sign:!sign thm in
      check_theorem ~bound:(bound_params ()) tys thm ;
      compile (CTheorem (name, tys, thm, Finished)) ;
      Artifact.add_lemma ~fin:Finished name tys thm
  | _ -> [%bug] "admit_theorem called on non-theorem"
  end ;
  ignore thm_id ;
  if not !Setup.annotate then Output.blank_line () ;
  Process_top

(* Called by [process_top1_body] when [--skip] applies. *)
(* Admits/ignores pre-target commands, else resumes normally. *)
and process_top1_body_skip () =
  let pre_lnum = (!Setup.lexbuf).Lexing.lex_curr_p.Lexing.pos_lnum in
  let any_input =
    Parser.any_command_start Lexer.token !Setup.lexbuf
  in
  let start_line =
    let (p1, _) = any_input.pos in
    if p1 == Lexing.dummy_pos then pre_lnum
    else p1.Lexing.pos_lnum
  in
  let is_before =
    match !Setup.skip_to with
    | Some (Setup.Skip_line n) -> start_line < n
    | Some (Setup.Skip_theorem _) -> not !Setup.skip_reached
    | None -> false
  in
  let is_target tc =
    match !Setup.skip_to, tc with
    | Some (Setup.Skip_theorem target), Theorem (nm, _, _) ->
        nm = target ||
        (Thmod.in_module () &&
         begin match Thmod.resolve_top tc with
         | Theorem (rn, _, _) -> rn = target
         | _ -> false
         end)
    | _ -> false
  in
  begin match any_input.el with
  | Types.ATopCommand tc ->
      let cmd_string = top_command_to_string tc in
      if is_target tc then Setup.skip_reached := true ;
      if is_before && not (is_target tc) then
        begin match tc with
        | Theorem _ -> admit_theorem tc any_input.pos cmd_string
        | _ -> run_top_command tc any_input.pos cmd_string
        end
      else
        run_top_command tc any_input.pos cmd_string
  | Types.ACommon cc ->
      let tc = Types.TopCommon cc in
      let cmd_string = top_command_to_string tc in
      run_top_command tc any_input.pos cmd_string
  | Types.ACommand _ ->
      if is_before then Process_top
      else
        begin match !Setup.skip_to with
        | Some (Setup.Skip_line n) ->
            failwithf
              "Cannot skip to line %d: inside proof" n
        | _ -> failwith "Stray proof command outside proof"
        end
  end

(* Called by [process_top1] as the top-level step. *)
(* Dispatches to normal or skip handling via [Setup.skip_to]. *)
and process_top1_body () =
  match !Setup.skip_to with
  | None -> process_top1_body_normal ()
  | Some _ ->
      if !Setup.mode = `interactive then process_top1_body_normal ()
      else process_top1_body_skip ()

and load_thm_artifact ~modname =
  Thm.Codec.load ~process:process1 ~init:Process_top ~modname

and load_thmod_artifact ~modname =
  Thmod.Codec.load ~process:process1 ~init:Process_top ~modname

(* Session snapshot and greeting *)

let initial_snapshot = State.snapshot ()

let () = Setup.initial_snapshot := Some initial_snapshot

let welcome_msg =
  Printf.sprintf "Welcome to Abella %s.\n" Version.version
