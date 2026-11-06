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
open Metaterm
open Checks
open Abella_types
open Typing
open Unifyty
open Extensions
open Printf
open Accumulate

module Setup = Driver_setup

let write_compilation () =
  match !Setup.file_kind with
  | `thmod -> Thmod.write_compilation ()
  | `thm -> Thm.write_compilation ()

let is_interactive () = !Setup.mode = `interactive

let in_module () = Thmod.current_name () <> None

let bound_params () =
  if in_module () then Thmod.all_params () else []

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

type processing_state =
  | Process_top
  | Process_proof of proof_processor

and proof_processor = {
  thm_id : int ;
  thm : string ;
  compile : fin -> unit ;
  reset : unit -> unit ;
}

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
    sprintf ": file %s, line %d, characters %d-%d" file line char1 char2

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

let compile citem =
  if !Setup.file_kind = `thmod || in_module () then
    Thmod.add_compiled citem
  else
    Thm.comp_content := citem :: !Thm.comp_content

let record_imported citem =
  if !Setup.file_kind = `thmod || in_module () then
    Thmod.add_imported_compiled citem
  else
    Thm.comp_content := citem :: !Thm.comp_content

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
          ~retype:Prover.retype
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
  | Abella_types.Reported_parse_error
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

let handle_search_witness w =
  if !Setup.witnesses then
    Output.msg_printf "Witness: %s." (witness_to_string w)

let term_witness (_t, w) =
  if !Setup.witnesses then
    Output.msg_printf "Witness: %s." (witness_to_string w)

let suppress_proof_state_display = State.rref false

let check_thmod_complete () =
  if !Setup.file_kind = `thmod then
    Thmod.check_complete ()

let handle_process_exception e =
  match e with
  | Abella_types.Reported_parse_error ->
      let pos = lexbuf_pos () in
      State.Undo.undo () ;
      Lexing.flush_input !Setup.lexbuf ;
      interactive_or_exit () ;
      Parse_error pos
  | Parser.Error ->
      let pos = lexbuf_pos () in
      State.Undo.undo () ;
      Output.msg_printf ~severity:Error
        "Syntax error%s." (position !Setup.lexbuf) ;
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
        | Setup.UserInterrupt -> User_interrupt
        | _ -> Runtime_error (sorry e)
      in
      Output.msg_printf ~severity:Error "Error: %s"
        (processing_error_to_string error) ;
      interactive_or_exit () ;
      error

let rec process1 state =
  State.Undo.push () ;
  try
    match state with
    | Process_top -> process_top1 state
    | Process_proof _ -> process_proof1 state
  with
  | End_of_file ->
      check_thmod_complete () ;
      write_compilation () ;
      begin match state with
      | Process_top ->
          if not (is_interactive ()) && !Setup.unfinished <> [] then begin
            Output.msg_printf "There were skips in these theorem(s): %s"
              (String.concat ", " (List.unique !Setup.unfinished))
          end ;
          if not (is_interactive ()) && !Setup.axioms <> [] then begin
            Output.msg_printf "The following axioms were used: %s"
              (String.concat ", " (List.unique (List.rev !Setup.axioms)))
          end ;
          Output.flush () ;
          raise @@ Setup.AbellaExit 0
      | _ ->
          Output.msg_printf ~severity:Error "Proof NOT Completed." ;
          Output.flush () ;
          raise @@ Setup.AbellaExit 1
      end

and process_proof1 state =
  match state with
  | Process_top ->
      [%bug] "process_proof1 called in top-level state"
  | Process_proof proc ->
      try
        process_proof1_body proc ;
        Ok (Process_proof proc)
      with
      | Prover.End_proof reason -> begin
          Output.msg_printf "Proof %s" begin
            match reason with
            | `completed fin -> begin
                proc.compile fin ;
                if fin = Unfinished then
                  Setup.unfinished := proc.thm :: !Setup.unfinished ;
                Printf.sprintf "completed%s"
                  (match fin with
                   | Finished | Axiomatic -> ""
                   | Unfinished -> " *** USING skip ***")
              end
            | `aborted -> "ABORTED"
          end ;
          proc.reset () ;
          (* print_clauses () ; *)
          Ok Process_top
        end
      | e -> Error (handle_process_exception e)

and process_proof1_body proc =
  if !Setup.mode = `interactive && not !suppress_proof_state_display then
    Output.non_annot "%s" @@ Prover.get_display () ;
  suppress_proof_state_display := false ;
  if !Setup.mode = `interactive then
    Output.non_annot "%s < " proc.thm ;
  let input = Parser.command_start Lexer.token !Setup.lexbuf in
  let cmd_string = command_to_string input.el in
  let input =
    if in_module () then
      { input with
        el = Thmod.resolve_proof_command ~is_hyp:Prover.is_hyp input.el }
    else
      input
  in
  if !Setup.mode <> `interactive then
    Output.non_annot "%s.\n" cmd_string ;
  let annot =
    if not !Setup.annotate then None else
    Output.message "proof_command" ~fields:begin
      [ "thm_id", `Int proc.thm_id ;
        "theorem", `String proc.thm ;
        "start_state", Prover.state_json () ;
        "command", `String cmd_string ] @
      (if fst input.pos = Lexing.dummy_pos then [] else
         [ "range", json_of_position input.pos ])
    end |> Option.some
  in
  let perform () =
    begin match input.el with
    | Induction(args, hn)           -> Prover.induction ?name:hn args
    | CoInduction hn                -> Prover.coinduction ?name:hn ()
    | Apply(depth, h, args, ws, hn) -> Prover.apply ?depth ?name:hn h args ws ~term_witness
    | Backchain(depth, h, ws)       -> Prover.backchain ?depth h ws ~term_witness
    | Compute (hs, gas, hn)         -> Compute.compute ?name:hn ?gas hs
    | ComputeAll (gas, hn, clr)     -> Compute.compute_all ?name:hn ?gas clr
    | Cut(h, arg, hn)               -> Prover.cut ?name:hn h arg
    | CutFrom(h, arg, t, hn)        -> Prover.cut_from ?name:hn h arg t
    | SearchCut(h, hn)              -> Prover.search_cut ?name:hn h
    | Inst(h, ws, hn)               -> Prover.inst ?name:hn h ws
    | Case(str, hn)                 -> Prover.case ?name:hn str
    | Assert(t, dp, hn)             ->
        untyped_ensure_no_restrictions t ;
        Prover.assert_hyp ?name:hn ?depth:dp t
    | Monotone(h, t, hn)            -> Prover.monotone ?name:hn h t
    | Exists(_, ts)                 -> List.iter Prover.exists ts
    | Clear(cm, hs)                 -> Prover.clear cm hs
    | ClearDups                     -> Prover.clear_duplicates ()
    | Abbrev(hs, s)                 -> Prover.abbrev (Iset.of_list hs) s
    | Unabbrev(hs)                  -> Prover.unabbrev (Iset.of_list hs)
    | Rename(hfr, hto)              -> Prover.rename hfr hto
    | Search(bounds) -> begin
        let depth = match bounds with
          | `depth n -> Some n
          | _ -> None
        in
        let witness = match bounds with
          | `witness w -> w
          | _ -> WMagic
        in
        Prover.search ?depth ~witness ~handle_witness:handle_search_witness ()
      end
    | Saturate sat           -> Prover.saturate sat.lemmas
                                  ?name:sat.hint ?depth:sat.depth
    | Permute(ids, h)        -> Prover.permute_nominals ids h
    | Split                  -> Prover.split false
    | SplitStar              -> Prover.split true
    | Left                   -> Prover.left ()
    | Right                  -> Prover.right ()
    | Unfold (cs, ss)        -> Prover.unfold cs ss
    | Intros hs              -> Prover.intros hs
    | Skip                   -> Prover.skip ()
    | Abort                  -> raise (Prover.End_proof `aborted)
    | Undo
    | Common(Back)           ->
        if !Setup.mode = `interactive then State.Undo.back 2
        else failwith "Cannot use interactive commands in non-interactive mode"
    | Common(Reset)          ->
        if !Setup.mode = `interactive then State.Undo.reset ()
        else failwith "Cannot use interactive commands in non-interactive mode"
    | Common(Set(k, v))      -> set k v
    | Common(Show nm)        ->
        Output.msg_format "%t" (Prover.show nm) ;
        if !Setup.mode = `interactive then Output.blank_line () ;
        suppress_proof_state_display := true
    | Common(ShowModule src) ->
        Thmod.show_module
          ~load:load_thmod_artifact src ;
        if !Setup.mode = `interactive then Output.blank_line () ;
        suppress_proof_state_display := true
    | Common(Quit)           -> raise End_of_file
    end
  in
  if not !Setup.annotate then perform () else
  match perform () with
  | () ->
      Option.iter begin fun annot ->
        Output.extend annot "end_state" @@ Prover.state_json ()
        |> Output.commit_message
      end annot
  | exception e ->
      Option.iter Output.commit_message annot ;
      raise e

and process_top1 state =
  match state with
  | Process_proof _ ->
      [%bug] "process_top1 called in proof state"
  | Process_top ->
      try Ok (process_top1_body ()) with
      | e -> Error (handle_process_exception e)

and process_top1_body () =
  if !Setup.mode = `interactive then Output.non_annot "Abella < " ;
  let input = Parser.top_command_start Lexer.token !Setup.lexbuf in
  let cmd_string = top_command_to_string input.el in
  let input =
    if in_module () then
      { input with el = Thmod.resolve_top input.el }
    else
      input
  in
  if !Setup.mode <> `interactive then Output.non_annot "%s.\n%!" cmd_string ;
  Thmod.check_structure input.el ;
  let thm_id =
    if not !Setup.annotate then -1 else
    let annot = Output.message "top_command" ~fields:begin
        (if fst input.pos = Lexing.dummy_pos then [] else
           ["range", json_of_position input.pos]) @
        [ "command", `String cmd_string ]
      end in
    Output.commit_message annot ;
    annot.id
  in
  let next_state = begin match input.el with
    | Theorem(name, tys, thm) -> begin
      let st = get_bind_state () in
      let seq = Prover.copy_sequent () in
      let thm = type_umetaterm ~sr:!sr ~sign:!sign thm in
      check_theorem ~bound:(bound_params ()) tys thm ;
      Prover.theorem thm ;
      let oldsign = !sign in
      let thm_compile fin =
        sign := oldsign ;
        compile (CTheorem(name, tys, thm, fin)) ;
        Artifact.add_lemma ~fin name tys thm
      in
      let thm_reset () =
        sign := oldsign ;
        Prover.reset_prover st seq ()
      in
      Prover.start_proof () ;
      if !Setup.annotate then
        Output.commit_message begin
          Output.message "theorem_state" ~fields:[
            "thm_id", `Int thm_id ;
            "theorem", `String name ;
            "state", Prover.state_json ()
          ]
        end ;
      Process_proof {
          thm_id ; thm = name ;
          compile = thm_compile ;
          reset = thm_reset
        }
    end
  | Axiom(name, tys, thm) ->
      let thm = type_umetaterm ~sr:!sr ~sign:!sign thm in
      check_theorem ~bound:(bound_params ()) tys thm ;
      compile (CTheorem(name, tys, thm, Axiomatic)) ;
      Artifact.add_lemma ~fin:Axiomatic name tys thm ;
      Setup.axioms := name :: !Setup.axioms ;
      Process_top
  | SSplit(name, names) ->
      let fin = Prover.get_lemma_tag name in
      let gen_thms =
        Prover.create_split_theorems name names |>
        List.map (fun (n, t) ->
            if in_module () then
              (Thmod.new_name n, t)
            else
              (n, t))
      in
      List.iter begin fun (n, (tys, t)) ->
        Output.msg_format "%t" (Prover.print_theorem n (tys, t)) ;
        Artifact.add_lemma ~fin n tys t ;
        compile (CTheorem(n, tys, t, fin))
      end gen_thms ;
      if fin = Unfinished && List.mem name !Setup.unfinished then
        Setup.unfinished :=
          List.map fst gen_thms @ !Setup.unfinished ;
      if fin = Axiomatic && not (List.mem name !Setup.axioms) then
        Setup.axioms :=
          name :: List.map fst gen_thms @ !Setup.axioms ;
      Process_top
  | Define _ ->
      let strat_errors =
        in_module () || !stratification_warnings_are_errors
      in
      compile (Prover.register_definition ~strat_errors
                 ~bound_tyvars:(bound_params ()) input.el) ;
      Process_top
  | Suspend (head, test) ->
      let g = Compute.make_guard ~head ~test in
      Compute.add_guard g ;
      (compile @@ CSuspend g) ;
      Process_top
  | TopCommon(Back) ->
      (if !Setup.mode = `interactive then State.Undo.back 2
       else
         failwith
           "Cannot use interactive commands in non-interactive mode") ;
      Process_top
  | TopCommon(Reset) ->
      (if !Setup.mode = `interactive then State.Undo.reset ()
       else
         failwith
           "Cannot use interactive commands in non-interactive mode") ;
      Process_top
  | TopCommon(Set(k, v)) -> set k v ; Process_top
  | TopCommon(Show(n)) ->
      Output.msg_format "%t" (Prover.show n) ; Process_top
  | TopCommon(ShowModule src) ->
      Thmod.show_module
        ~load:load_thmod_artifact src ;
      Process_top
  | TopCommon(Quit) -> raise End_of_file
  | Import(filename, pos, withs) ->
      compile (CImport (filename, withs)) ;
      Thm.import ~load:load_thm_artifact
        ~wrt:!Setup.input pos filename withs ;
      Process_top
  | Module (name, params) ->
      Thmod.process_module name params ;
      Process_top
  | End name ->
      Thmod.process_end name ;
      Process_top
  | ImportModule mi ->
      begin match mi.mi_source with
      | QuoteSource (file, pos) ->
          if !Setup.annotate then begin
            let file = Filepath.normalize ~wrt:!Setup.input file in
            Output.link_message ~pos ~url:(file ^ ".html")
          end
      | NameSource _ -> ()
      end ;
      Thmod.import_module
        ~load:load_thmod_artifact
        ~record:record_imported mi ;
      Process_top
  | Specification(filename, pos) ->
      (if !Thm.can_read_specification then begin
         let filename = Filepath.normalize ~wrt:!Setup.input filename in
         Thm.read_specification filename ;
         Thm.ensure_finalized_specification () ;
         if !Setup.annotate then
           Output.link_message ~pos ~url:(filename ^ ".lp.html") ;
       end else
         failwith "Specification can only be read \
                  \ at the begining of a development.") ;
      Process_top
  | Query(q) -> query q ; Process_top
  | Kind(ids,knd) ->
      check_noredef ids;
      Prover.add_global_types ids knd;
      compile (CKind (ids,knd)) ;
      Process_top
  | Type(ids, ty) ->
      check_noredef ids ;
      let is_declared_predicate =
        match observe_ty ty with
        | Ty (_, aty) -> aty = propaty
      in
      let typarams =
        if in_module () && is_declared_predicate &&
           contains_prop_argument ty then begin
          let name = match ids with
            | id :: _ -> id
            | [] -> "<unknown>"
          in
          failwithf
            "Declared predicate %s may not take an argument containing prop"
            name
        end else
          List.minus (get_typaram ty) (bound_params ())
      in
      Prover.add_global_consts ~typarams
        (List.map (fun id -> (id, ty)) ids) ;
      let comp =
        if in_module () && is_declared_predicate
        then CDeclPred (ids, typarams, ty)
        else CType (ids, typarams, ty)
      in
      compile comp ;
      Process_top
  | Close(atys) ->
      Prover.close_types !sign !Prover.clauses atys ;
      compile (CClose(List.map (fun aty ->
        (aty, Subordination.subordinates !sr aty)) atys)) ;
      Process_top
  end
  in
  if not !Setup.annotate then Output.blank_line () ;
  next_state

and[@inline] load_thm_artifact ~modname =
  Thm.Codec.load ~process:process1 ~init:Process_top ~modname

and[@inline] load_thmod_artifact ~modname =
  Thmod.Codec.load ~process:process1 ~init:Process_top ~modname

let initial_snapshot = State.snapshot ()

let welcome_msg = sprintf "Welcome to Abella %s.\n" Version.version
