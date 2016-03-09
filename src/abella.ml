(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
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
open Prover
open Checks
open Abella_types
open Typing
open Extensions
open Printf
open Accumulate

let can_read_specification = State.rref true

let interactive = ref true
let compile_out = ref None

let switch_to_interactive = ref false
let lexbuf = ref (Lexing.from_channel stdin)

let annotate = ref false

let count = ref 0

let witnesses = State.rref false

exception AbortProof

exception UserInterrupt

let eprintf fmt = fprintf !out fmt

(* Input *)

let perform_switch_to_interactive () =
  assert !switch_to_interactive ;
  switch_to_interactive := false ;
  lexbuf := Lexing.from_channel stdin ;
  interactive := true ;
  out := stdout ;
  fprintf !out "Switching to interactive mode.\n%!" ;
  State.Undo.undo ()

let interactive_or_exit () =
  if not !interactive then
    if !switch_to_interactive then
      perform_switch_to_interactive ()
    else
      exit 1

let position_range (p1, p2) =
  let file = p1.Lexing.pos_fname in
  let line = p1.Lexing.pos_lnum in
  let char1 = p1.Lexing.pos_cnum - p1.Lexing.pos_bol in
  let char2 = p2.Lexing.pos_cnum - p1.Lexing.pos_bol in
  if file = "" then
    ""
  else
    sprintf ": file %s, line %d, characters %d-%d" file line char1 char2

let type_inference_error (pos, ct) exp act =
  fprintf !out "Typing error%s.\n%!" (position_range pos) ;
  match ct with
  | CArg ->
      eprintf "Expression has type %s but is used here with type %s\n%!"
        (ty_to_string act) (ty_to_string exp)
  | CFun ->
      eprintf "Expression is applied to too many arguments\n%!"

let teyjus_only_keywords =
  ["closed"; "exportdef"; "import"; "infix"; "infixl"; "infixr"; "local";
   "localkind"; "postfix"; "posfixl"; "prefix"; "prefixr"; "typeabbrev";
   "use_sig"; "useonly"; "sigma"]

let warn_on_teyjus_only_keywords (ktable, ctable) =
  let tokens = List.unique (ktable @ List.map fst ctable) in
  let used_keywords = List.intersect tokens teyjus_only_keywords in
  if used_keywords <> [] then
    fprintf !out
      "Warning: The following tokens are keywords in Teyjus: %s\n%!"
      (String.concat ", " used_keywords)

let update_subordination_sign sr sign =
  List.fold_left Subordination.update sr (sign_to_tys sign)

let read_specification name =
  clear_specification_cache () ;
  fprintf !out "Reading specification %S%s\n%!" name
    (if !load_path <> "." then
       sprintf " (from %S)" !load_path
     else "") ;
  let read_sign = get_sign name in
  let () = warn_on_teyjus_only_keywords read_sign in
  let sign' = merge_signs [!sign; read_sign] in
  let sr' = update_subordination_sign !sr read_sign in
  let clauses' = get_clauses ~sr:sr' name in
  (* Any exceptions must have been thrown by now - do actual assignments *)
  sr := sr' ;
  sign := sign' ;
  add_clauses clauses'


(* Compilation and importing *)

let comp_spec_sign = State.rref ([], [])
let comp_spec_clauses = State.rref []
let comp_content = State.rref []

let marshal citem =
  match !compile_out with
  | Some cout -> Marshal.to_channel cout citem []
  | None -> ()

let ensure_finalized_specification () =
  if !can_read_specification then begin
    can_read_specification := false ;
    comp_spec_sign := !sign ;
    comp_spec_clauses := !clauses
  end

let compile citem =
  ensure_finalized_specification () ;
  comp_content := citem :: !comp_content

let predicates (ktable, ctable) =
  ctable |>
  List.filter_map begin fun (id, Poly (_, Ty (_, targty))) ->
    if List.mem id [k_member ; k_fresh ; k_name] || targty = "o" then None
    else Some id
  end

let write_compilation () =
  marshal Version.self_digest ;
  marshal Version.version ;
  marshal !comp_spec_sign ;
  marshal !comp_spec_clauses ;
  marshal (predicates !sign) ;
  marshal (List.rev !comp_content)

let clause_eq c1 c2 = eq c1 c2

let clauses_to_predicates clauses =
  let clause_heads =
    List.map (fun c -> let (_,h,_) = clausify c in h) clauses in
  List.unique (List.map term_head_name clause_heads)

let ensure_valid_import imp_spec_sign imp_spec_clauses imp_predicates =
  let (ktable, ctable) = !sign in
  let (imp_ktable, imp_ctable) = imp_spec_sign in
  let imp_ctable = List.filter begin
      fun (id, ty) ->
        match ty with
        | Typing.Poly (_, Ty (_, "prop")) -> false
        | _ -> true
    end imp_ctable in

  (* 1. Imported ktable must be a subset of ktable *)
  let missing_types = List.minus imp_ktable ktable in
  let () = if missing_types <> [] then
      failwithf "Imported file makes reference to unknown types: %s"
        (String.concat ", " missing_types)
  in

  (* 2. Imported ctable must be a subset of ctable *)
  let missing_consts = List.minus imp_ctable ctable in
  let () = if missing_consts <> [] then
      failwithf "Imported file makes reference to unknown constants: %s"
        (String.concat ", " (List.map fst missing_consts))
  in

  (* 3. Imported clauses must be a subset of clauses *)
  let missing_clauses =
    List.minus ~cmp:clause_eq imp_spec_clauses !clauses
  in
  let () = if missing_clauses <> [] then
      failwithf "Imported file makes reference to unknown clauses for: %s"
        (String.concat ", " (clauses_to_predicates missing_clauses))
  in

  (* 4. Clauses for imported predicates must be subset of imported clauses *)
  let extended_clauses =
    List.minus ~cmp:clause_eq
      (List.find_all
         (fun clause ->
            let (_,clause_head,_) = clausify clause in
            List.mem (term_head_name clause_head) imp_predicates)
         !clauses)
      imp_spec_clauses
  in
  let () = if extended_clauses <> [] then
      failwithf "Cannot import file since clauses have been extended for: %s"
        (String.concat ", " (clauses_to_predicates extended_clauses))
  in
  ()


let imported = State.rref []

let maybe_make_importable ?(force=false) root =
  let thc = root ^ ".thc" in
  let thm = root ^ ".thm" in
  let force = force || begin
      Sys.file_exists thm && begin
        not (Sys.file_exists thc) || begin
          let thmstat = Unix.stat thm in
          let thcstat = Unix.stat thc in
          thmstat.Unix.st_mtime > thcstat.Unix.st_mtime
        end
      end
    end in
  if not !Sys.interactive && force then
    let cmd = Printf.sprintf "%s %s -o %s.out -c %s" Sys.executable_name thm root thc in
    Printf.eprintf "Running: %S.\n%!" cmd ;
    if Sys.command cmd <> 0 then
      failwithf "Could not create %S" thc

let replace_atom_term decl defn_name defn t =
  let ty = tc [] defn in
  let t = Term.abstract decl ty t in
  let rt = Term.app t [defn] in
  (* Printf.printf "Rewrote %s to %s\n%!" (term_to_string t) (term_to_string rt) ; *)
  rt

let replace_atom_metaterm decl defn_name defn mt =
  let rmt = map_terms (replace_atom_term decl defn_name defn) mt in
  (* Printf.printf "Rewrote %s to %s\n%!" (metaterm_to_string mt) (metaterm_to_string rmt) ; *)
  rmt

let replace_atom_clause decl defn_name defn cl =
  let head = replace_atom_metaterm decl defn_name defn cl.head in
  let body = replace_atom_metaterm decl defn_name defn cl.body in
  { head ; body }

let replace_atom_block decl defn_name defn bl =
  { bl with
    bl_rel =
      List.map (fun ts -> List.map (replace_atom_term decl defn_name defn) ts)
        bl.bl_rel }

let replace_atom_schema decl defn_name defn sch =
  { sch with
    sch_blocks = List.map (replace_atom_block decl defn_name defn) sch.sch_blocks }

let replace_atom_compiled decl defn_name defn comp=
  match comp with
  | CTheorem (nm, tyvars, bod) ->
      (* Printf.printf "Trying to rewrite a CTheorem\n%!" ; *)
      CTheorem (nm, tyvars, replace_atom_metaterm decl defn_name defn bod)
  | CDefine (flav, tyvars, definiens, clauses) ->
      if List.mem_assoc defn_name definiens then
        failwithf "There is already a defined atom named %s in import" defn_name ;
      (* Printf.printf "Trying to rewrite a CDefine\n%!" ; *)
      CDefine (flav, tyvars, definiens,
               List.map (replace_atom_clause decl defn_name defn) clauses)
  | CSchema sch ->
      (* Printf.printf "Trying to rewrite a CSchema\n%!" ; *)
      CSchema (replace_atom_schema decl defn_name defn sch)
  | CImport (fn, ws) ->
      (* Printf.printf "Trying to rewrite a CImport\n%!" ; *)
      let ws = List.map begin fun (wfrom, wto) ->
          if wto = decl then (wfrom, defn_name)
          else (wfrom, wto)
        end ws in
      CImport (fn, ws)
  | CKind ids ->
      (* Printf.printf "Trying to rewrite a CKind\n%!" ; *)
      if List.mem defn_name ids then
        failwithf "There are declared types named %s in import" defn_name ;
      comp
  | CType (ids, _) ->
      (* Printf.printf "Trying to rewrite a CType\n%!" ; *)
      if List.mem defn_name ids then
        failwithf "There are declared constants named %s in import" defn_name ;
      comp
  | CClose _ ->
      (* Printf.printf "Trying to rewrite a CClose\n%!" ; *)
      comp

let import filename withs =
  let rec aux filename withs =
    maybe_make_importable filename ;
    if not (List.mem filename !imported) then begin
      imported := filename :: !imported ;
      let thc = filename ^ ".thc" in
      let file =
        let ch = open_in_bin thc in
        let dig = (Marshal.from_channel ch : Digest.t) in
        let ver = (Marshal.from_channel ch : string) in
        if dig <> Version.self_digest then begin
          Printf.printf
            "Warning: %S was compiled with a different version (%s) of Abella; recompiling...\n%!"
            thc ver ;
          close_in ch ;
          maybe_make_importable ~force:true filename ;
          let ch = open_in_bin thc in
          ignore (Marshal.from_channel ch : Digest.t) ;
          ignore (Marshal.from_channel ch : string) ;
          ch
        end else ch
      in
      let imp_spec_sign = (Marshal.from_channel file : sign) in
      let imp_spec_clauses = (Marshal.from_channel file : clause list) in
      let imp_predicates = (Marshal.from_channel file : string list) in
      let imp_content = (Marshal.from_channel file : compiled list) in
      ensure_valid_import imp_spec_sign imp_spec_clauses imp_predicates ;
      let rec process_decls decls =
        match decls with
        | [] -> ()
        | decl :: decls -> begin
            match decl with
            | CTheorem(name, tys, thm) ->
                add_lemma name tys thm ;
                process_decls decls
            | CDefine(flav, tyargs, idtys, clauses) ->
                let ids = List.map fst idtys in
                check_noredef ids;
                let (basics, consts) = !sign in
                let consts = List.map (fun (id, ty) -> (id, Poly (tyargs, ty))) idtys @ consts in
                sign := (basics, consts) ;
                add_defs tyargs idtys flav clauses ;
                process_decls decls
            | CSchema sch ->
                Schemas.register_typed_schema sch ;
                process_decls decls
            | CImport(filename, withs) ->
                aux filename withs ;
                process_decls decls
            | CKind(ids) ->
                check_noredef ids ;
                add_global_types ids ;
                process_decls decls
            | CType(ids, (Ty(_, "prop") as ty)) -> begin
                (* Printf.printf "Need to instantiate: %s\n%!" (String.concat ", " ids) ; *)
                let instantiate_id decls id =
                  try begin
                    let open Typing in
                    let pred_name = List.assoc id withs in
                    let pred = UCon (ghost, pred_name, Term.fresh_tyvar ()) in
                    let pred = type_uterm ~sr:!sr ~sign:!sign ~ctx:[] pred in
                    let pred_ty = tc [] pred in
                    tid_ensure_fully_inferred ~sign:!sign (pred_name, pred_ty) ;
                    if ty <> pred_ty then
                      failwithf "Expected type %s:%s, got %s:%s"
                        id (ty_to_string ty)
                        pred_name (ty_to_string pred_ty) ;
                    List.map (replace_atom_compiled id pred_name pred) decls
                  end with Not_found ->
                    failwithf "Missing instantiation for %s" id
                in
                List.fold_left instantiate_id decls ids |>
                process_decls
              end
            | CType(ids,ty) ->
                check_noredef ids ;
                add_global_consts (List.map (fun id -> (id, ty)) ids) ;
                process_decls decls
            | CClose(ty_subords) ->
                List.iter
                  (fun (ty, prev) ->
                     let curr = Subordination.subordinates !sr ty in
                     match List.minus curr prev with
                     | [] -> ()
                     | xs ->
                         failwithf
                           "Cannot close %s since it is now subordinate to %s"
                           ty (String.concat ", " xs))
                  ty_subords ;
                close_types (List.map fst ty_subords) ;
                process_decls decls
          end
      in
      process_decls imp_content
    end
  in
  if List.mem filename !imported then
    fprintf !out "Ignoring import: %s has already been imported.\n%!" filename
  else begin
    fprintf !out "Importing from %s\n%!" filename ;
    aux filename withs
  end


(* Proof processing *)

let query q =
  let fv = ids_to_fresh_tyctx (umetaterm_extract_if is_capital_name q) in
  let ctx = fresh_alist ~tag:Logic ~used:[] fv in
  match type_umetaterm ~sr:!sr ~sign:!sign ~ctx (UBinding(Metaterm.Exists, fv, q)) with
  | Binding(Metaterm.Exists, fv, q) ->
      let support = metaterm_support q in
      let ctx = Tactics.fresh_nameless_alist ~support ~ts:0 ~tag:Logic fv in
      let q = replace_metaterm_vars ctx q in
      let _ = Tactics.search q
          ~depth:max_int
          ~hyps:[]
          ~clauses:!clauses
          ~def_unfold:Prover.def_unfold
          ~retype
          ~sc:(fun w ->
              fprintf !out "Found solution:\n" ;
              List.iter
                (fun (n, v) ->
                   fprintf !out "%s = %s\n" n (term_to_string v))
                ctx ;
              fprintf !out "\n%!")
      in
      fprintf !out "No more solutions.\n%!"
  | _ -> assert false

let set_fail ~key ~expected v =
  failwithf "Unknown value '%s' for key %S; expected %s"
    (set_value_to_string v) key expected

let set_subgoal_max_spec spec =
  let buf = Lexing.from_string spec in
  let spec = Parser.depth_spec Lexer.token buf in
  set_subgoal_max spec

let set k v =
  match k, v with
  | "subgoals", Int d when d >= 0 ->
      reset_subgoal_max () ;
      set_subgoal_max [d, Some max_int]
  | "subgoals", Str "on" ->
      reset_subgoal_max () ;
      set_subgoal_max_default max_int
  | "subgoals", Str "off" ->
      reset_subgoal_max () ;
      set_subgoal_max_default 0
  | "subgoals", QStr spec ->
      set_subgoal_max_spec spec
  | "subgoals", _ -> set_fail v
                       ~key:"subgoals"
                       ~expected:"'on', 'off', non-negative integer, or depth specification"

  | "instantiations", Str "on" -> Prover.show_instantiations := true
  | "instantiations", Str "off" -> Prover.show_instantiations := false
  | "instantiations", _ -> set_fail v
                             ~key:"instantiations"
                             ~expected:"'on' or 'off'"

  | "types", Str "on" -> Metaterm.show_types := true
  | "types", Str "off" -> Metaterm.show_types := false
  | "types", _ -> set_fail v
                    ~key:"types"
                    ~expected:"'on' or 'off'"

  | "search_depth", Int d when d >= 0 -> search_depth := d
  | "search_depth", _ -> set_fail v
                           ~key:"search_depth"
                           ~expected:"non-negative integer"

  | "witnesses", Str "on" -> witnesses := true
  | "witnesses", Str "off" -> witnesses := false
  | "witnesses", _ -> set_fail v
                        ~key:"witnesses"
                        ~expected:"'on' or 'off'"

  | "load_path", QStr s -> load_path := s

  | _, _ -> failwithf "Unknown key '%s'" k

let handle_search_witness w =
  if !witnesses then
    fprintf !out "Witness: %s\n%!" (witness_to_string w)

let term_witness (t, w) =
  if !witnesses then
    fprintf !out "Witness: %s\n%!" (witness_to_string w)

let suppress_proof_state_display = State.rref false

type processing_state =
  | Process_top
  | Process_proof of proof_processor

and proof_processor = {
  thm : string ;
  compile : (unit -> unit) ;
  reset : (unit -> unit) ;
}

let current_state = State.rref Process_top

let rec process1 () =
  State.Undo.push () ;
  try begin match !current_state with
    | Process_top ->
        process_top1 ()
    | Process_proof proc -> begin
        try process_proof1 proc.thm with
        | Prover.End_proof reason -> begin
            fprintf !out "Proof %s.\n%!" begin
              match reason with
              | `completed ->
                  proc.compile () ;
                  "completed"
              | `aborted -> "ABORTED"
            end ;
            proc.reset () ;
            current_state := Process_top
          end
      end
  end with
  | Abella_types.Reported_parse_error ->
      State.Undo.undo () ;
      Lexing.flush_input !lexbuf ;
      interactive_or_exit ()
  | Parsing.Parse_error ->
      State.Undo.undo () ;
      eprintf "Syntax error%s.\n%!" (position !lexbuf) ;
      Lexing.flush_input !lexbuf ;
      interactive_or_exit ()
  | TypeInferenceFailure(ci, exp, act) ->
      State.Undo.undo () ;
      type_inference_error ci exp act ;
      interactive_or_exit ()
  | End_of_file ->
      write_compilation () ;
      if !switch_to_interactive then begin
        if !annotate then fprintf !out "\n</pre>\n" ;
        perform_switch_to_interactive ()
      end else begin
        match !current_state with
        | Process_top ->
            if !annotate then fprintf !out "\n</pre>\n%!" ;
            exit 0
        | _ ->
            fprintf !out "Proof NOT completed.\n%!" ;
            if !annotate then fprintf !out "</pre>\n%!" ;
            exit 1
      end
  | e ->
      State.Undo.undo () ;
      let msg = match e with
        | Failure msg -> msg
        | Unify.UnifyFailure fl -> Unify.explain_failure fl
        | Unify.UnifyError err -> Unify.explain_error err
        | UserInterrupt -> "Interrupted (use ctrl-D to quit)"
        | _ ->
            Printexc.to_string e ^ "\n\n\
                                   \ Sorry for displaying a naked OCaml exception. An informative error message\n\
                                   \ has not been designed for this situation.\n\n\
                                   \ To help improve Abella's error messages, please file a bug report at\n\
                                   \ <https://github.com/abella-prover/abella/issues>. Thanks!"
      in
      eprintf "Error: %s\n%!" msg ;
      interactive_or_exit ()

and process_proof1 name =
  if not !suppress_proof_state_display then begin
    display !out ;
  end ;
  suppress_proof_state_display := false ;
  fprintf !out "%s < %!" name ;
  let input = Parser.command Lexer.token !lexbuf in
  if not !interactive then begin
    let pre, post = if !annotate then "<b>", "</b>" else "", "" in
    fprintf !out "%s%s.%s\n%!" pre (command_to_string input) post
  end ;
  begin match input with
  | Induction(args, hn)      -> induction ?name:hn args
  | CoInduction hn           -> coinduction ?name:hn ()
  | Apply(h, args, ws, hn)   -> apply ?name:hn h args ws ~term_witness
  | Backchain(depth, h, ws)  -> backchain ?depth h ws ~term_witness
  | Cut(h, arg, hn)          -> cut ?name:hn h arg
  | CutFrom(h, arg, t, hn)   -> cut_from ?name:hn h arg t
  | SearchCut(h, hn)         -> search_cut ?name:hn h
  | Inst(h, ws, hn)          -> inst ?name:hn h ws
  | Case(str, hn)            -> case ?name:hn str
  | Assert(t, hn)            ->
      untyped_ensure_no_restrictions t ;
      assert_hyp ?name:hn t
  | Pick(depth, bs, t)      -> pick ?depth bs t
  | Exists(_, t)             -> exists t
  | Monotone(h, t)           -> monotone h t
  | Clear(hs)                -> clear hs
  | Abbrev(h, s)             -> abbrev h s
  | Unabbrev(hs)             -> unabbrev hs
  | Rename(hfr, hto)         -> rename hfr hto
  | Search(bounds) -> begin
      let depth = match bounds with
        | `depth n -> Some n
        | _ -> None
      in
      let witness = match bounds with
        | `witness w -> w
        | _ -> WMagic
      in
      search ?depth ~interactive:!interactive ~witness ~handle_witness:handle_search_witness ()
    end
  | Permute(ids, h)        -> permute_nominals ids h
  | Split                  -> split false
  | SplitStar              -> split true
  | Left                   -> left ()
  | Right                  -> right ()
  | Unfold (cs, ss)        -> unfold cs ss
  | Intros hs              -> intros hs
  | Skip                   -> skip ()
  | Abort                  -> raise (End_proof `aborted)
  | Undo
  | Common(Back)           ->
      if !interactive then State.Undo.back 2
      else failwith "Cannot use interactive commands in non-interactive mode"
  | Common(Reset)          ->
      if !interactive then State.Undo.reset ()
      else failwith "Cannot use interactive commands in non-interactive mode"
  | Common(Set(k, v))      -> set k v
  | Common(Show nm)        ->
      show nm ;
      fprintf !out "\n%!" ;
      suppress_proof_state_display := true
  | Common(Quit)           -> raise End_of_file
  end

and process_top1 () =
  fprintf !out "Abella < %!" ;
  let input = Parser.top_command Lexer.token !lexbuf in
  if not !interactive then begin
    let pre, post = if !annotate then "<b>", "</b>" else "", "" in
    fprintf !out "%s%s.%s\n%!" pre (top_command_to_string input) post
  end ;
  begin match input with
  | Theorem(name, tys, thm) ->
      let tsign =
        let (basics, consts) = !sign in
        if List.exists (fun t -> List.mem t basics) tys then
          failwithf "This basic type is already in scope: %s"
            (List.find (fun t -> List.mem t basics) tys) ;
        (tys @ basics, consts)
      in
      let thm = type_umetaterm ~sr:!sr ~sign:tsign thm in
      check_theorem thm ;
      theorem thm ;
      let oldsign = !sign in
      let thm_compile () =
        sign := oldsign ;
        compile (CTheorem(name, tys, thm)) ;
        add_lemma name tys thm
      in
      let thm_reset () =
        sign := oldsign ;
        reset_prover ()
      in
      sign := tsign ;
      current_state := Process_proof {
          thm = name ;
          compile = thm_compile ;
          reset = thm_reset
        } ;
  | SSplit(name, names) ->
      let gen_thms = create_split_theorems name names in
      List.iter begin fun (n, (tys, t)) ->
        print_theorem n (tys, t) ;
        add_lemma n tys t ;
        compile (CTheorem(n, tys, t))
      end gen_thms ;
  | Define _ ->
      compile (register_definition input)
  | Schema sch ->
      Schemas.register_schema sch
  | TopCommon(Back) ->
      if !interactive then State.Undo.back 2
      else failwith "Cannot use interactive commands in non-interactive mode"
  | TopCommon(Reset) ->
      if !interactive then State.Undo.reset ()
      else failwith "Cannot use interactive commands in non-interactive mode"
  | TopCommon(Set(k, v)) -> set k v
  | TopCommon(Show(n)) -> show n
  | TopCommon(Quit) -> raise End_of_file
  | Import(filename, withs) ->
      compile (CImport (filename, withs)) ;
      import filename withs;
  | Specification(filename) ->
      if !can_read_specification then begin
        read_specification filename ;
        ensure_finalized_specification ()
      end else
        failwith "Specification can only be read \
                 \ at the begining of a development."
  | Query(q) -> query q
  | Kind(ids) ->
      check_noredef ids;
      add_global_types ids ;
      compile (CKind ids)
  | Type(ids, ty) ->
      check_noredef ids;
      add_global_consts (List.map (fun id -> (id, ty)) ids) ;
      compile (CType(ids, ty))
  | Close(ids) ->
      close_types ids ;
      compile (CClose(List.map (fun id -> (id, Subordination.subordinates !sr id)) ids))
  end ;
  if !interactive then flush stdout ;
  fprintf !out "\n%!"

(* Command line and startup *)

let welcome_msg = sprintf "Welcome to Abella %s\n" Version.version

let usage_message = Printf.sprintf "%s [options] <theorem-file>" begin
    if !Sys.interactive then "abella" else Filename.basename Sys.executable_name
  end

let set_output filename =
  out := open_out filename

let set_compile_out filename =
  compile_out := Some (open_out_bin filename)

let makefile = ref false

let parse_value v =
  if String.length v < 1 then bugf "parse_value" ;
  match v.[0] with
  | '0' .. '9' -> Int (int_of_string v)
  | '"' -> QStr (String.sub v 1 (String.length v - 2))
  | _ -> Str v

let set_flags flagstr =
  try begin
    flagstr |>
    String.split ~test:(fun c -> c = ',') |>
    List.map (String.split ~test:(fun c -> c = '=')) |>
    List.iter begin function
    | [k ; v] -> set k (parse_value v)
    | [k]     -> set k (Str "on")
    | _       -> bugf "set_flags: %S" flagstr
    end
  end with
  | Invalid_argument msg | Failure msg ->
      raise (Arg.Bad msg)
  | e ->
      raise (Arg.Bad (Printexc.to_string e))

let options =
  Arg.align [
    "-f", Arg.String set_flags,
    "<flags> Initialize flags based on a comma-separate list of key=value pairs" ;

    "-i", Arg.Set switch_to_interactive,
    " Switch to interactive mode after reading inputs" ;

    "-o", Arg.String set_output, "<file-name> Output to file" ;

    "-c", Arg.String set_compile_out,
    "<file-name> Compile definitions and theorems in an importable format" ;

    "-a", Arg.Set annotate, " Annotate mode" ;

    "-M", Arg.Set makefile, " Output dependencies in Makefile format" ;
  ]

let input_files = ref []

let set_input () =
  match !input_files with
    | [] -> ()
    | [filename] ->
        interactive := false ;
        lexbuf := lexbuf_from_file filename
    | fs ->
        eprintf "Error: Multiple files specified as input: %s\n%!"
          (String.concat ", " fs) ;
        exit 1

let add_input filename =
  input_files := !input_files @ [filename]

let number fn () =
  if !annotate then begin
    incr count ;
    fprintf !out "<a name=\"%d\"></a>\n%!" !count ;
    fprintf !out "<pre class=\"code\">\n%!" ;
  end ;
  fn () ;
  if !annotate then fprintf !out "</pre>\n%!"

let _ =
  Sys.set_signal Sys.sigint
    (Sys.Signal_handle (fun _ -> raise UserInterrupt)) ;

  Arg.parse options add_input usage_message ;

  if not !Sys.interactive then
    if !makefile then begin
      List.iter Depend.print_deps !input_files ;
    end else begin
      set_input () ;
      fprintf !out "%s%!" welcome_msg ;
      State.Undo.set_enabled (!interactive || !switch_to_interactive) ;
      while true do number process1 () done
    end
;;
