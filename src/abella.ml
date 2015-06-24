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

(* BEGIN global Abella configuration *)

let stratification_warnings_are_errors = false
  (** Any stratification violation warnings are treated as errors *)

(* END global Abella configuration *)

open Term
open Metaterm
open Prover
open Abella_types
open Typing
open Extensions
open Printf
open Accumulate

let can_read_specification = State.rref true

let interactive = ref true
let out = ref stdout
let compile_out = ref None

let switch_to_interactive = ref false
let lexbuf = ref (Lexing.from_channel stdin)

let annotate = ref false
let count = ref 0

let witnesses = State.rref false

exception AbortProof

(* Input *)

let perform_switch_to_interactive () =
  assert !switch_to_interactive ;
  switch_to_interactive := false ;
  lexbuf := Lexing.from_channel stdin ;
  interactive := true ;
  out := stdout ;
  fprintf !out "Switching to interactive mode.\n%!"

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
  eprintf "Typing error%s.\n%!" (position_range pos) ;
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

(* Checks *)

let ensure_no_restrictions term =
  if get_max_restriction term > 0 then
    failwithf "Invalid formula: %s\n\
             \ Cannot use size restrictions (*, @, #, or +)"
      (metaterm_to_string term)

let untyped_ensure_no_restrictions term =
  ensure_no_restrictions (umetaterm_to_metaterm [] term)

let rec contains_prop ty =
  match ty with
  | Ty (argtys, targty) ->
      targty = "prop" || List.exists contains_prop argtys

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
  iter_preds begin fun ~parity ~posity t ->
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

let check_theorem thm =
  ensure_no_restrictions thm

let ensure_not_capital name =
  if is_capital_name name then
    failwithf "Invalid defined predicate name %S.\n\
             \ Defined predicates may not begin with a capital letter."
      name

let ensure_name_contained id ids =
  if not (List.mem id ids) then
    failwithf "Found stray clause for %s" id

let ensure_wellformed_head t =
  match t with
    | Pred _ -> ()
    | Binding(Nabla, _, Pred _) -> ()
    | _ ->
        failwithf "Invalid head in definition: %s"
          (metaterm_to_string t)

let check_def_clauses names defs =
  List.iter ensure_not_capital names ;
  List.iter
    (fun {head ; body} ->
       ensure_wellformed_head head ;
       ensure_name_contained (def_head_name head) names ;
       ensure_no_restrictions head ;
       ensure_no_restrictions body ;
       warn_stratify names head body)
    defs

let check_noredef ids =
  let (_, ctable) = !sign in
    List.iter (
      fun id -> if List.mem id (List.map fst ctable) then
        failwithf "Predicate or constant %s already exists" id
    ) ids

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
  List.map fst (List.find_all (fun (_, Poly(_, Ty(_, ty))) -> ty = "o") ctable)

let write_compilation () =
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


let imported = ref []

let import filename =
  let rec aux filename =
    if not (List.mem filename !imported) then begin
      imported := filename :: !imported ;
      let file = open_in_bin (filename ^ ".thc") in
      let imp_spec_sign = (Marshal.from_channel file : sign) in
      let imp_spec_clauses = (Marshal.from_channel file : clause list) in
      let imp_predicates = (Marshal.from_channel file : string list) in
      let imp_content = (Marshal.from_channel file : compiled list) in
        ensure_valid_import imp_spec_sign imp_spec_clauses imp_predicates ;
        List.iter
          (function
             | CTheorem(name, tys, thm) ->
                 add_lemma name tys thm ;
             | CDefine(flav, idtys, defs) ->
                 let ids = List.map fst idtys in
                   check_noredef ids;
                   check_def_clauses ids defs ;
                   add_global_consts idtys ;
                   add_defs ids flav defs ;
             | CSchema sch ->
                 bugf "Schemas not yet supported"
             | CImport(filename) ->
                 aux filename
             | CKind(ids) ->
                 check_noredef ids;
                 add_global_types ids
             | CType(ids, ty) ->
                 check_noredef ids;
                 add_global_consts (List.map (fun id -> (id, ty)) ids)
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
                 close_types (List.map fst ty_subords))
          imp_content
    end
  in
    if List.mem filename !imported then
      fprintf !out "Ignoring import: %s has already been imported.\n%!" filename
    else begin
      fprintf !out "Importing from %s\n%!" filename ;
      aux filename
    end


(* Proof processing *)

let query q =
  let fv = ids_to_fresh_tyctx (umetaterm_extract_if is_capital_name q) in
  let ctx = fresh_alist ~tag:Logic ~used:[] fv in
  match type_umetaterm ~sr:!sr ~sign:!sign ~ctx (UBinding(Metaterm.Exists, fv, q)) with
    | Binding(Metaterm.Exists, fv, q) ->
        let ctx = List.map begin fun (x, ty) ->
            (x, Term.fresh ~tag:Logic 0 ty)
          end fv in
        let q = replace_metaterm_vars ctx q in
        let _ = Tactics.search
          ~depth:max_int
          ~hyps:[]
          ~clauses:!clauses
          ~get_defs:Prover.get_defs
          ~sc:(fun w ->
                 fprintf !out "Found solution:\n" ;
                 List.iter
                   (fun (n, v) ->
                      fprintf !out "%s = %s\n" n (term_to_string v))
                   ctx ;
                 fprintf !out "\n%!")
          q
        in
          fprintf !out "No more solutions.\n%!"
    | _ -> assert false

let set_fail ~key ~expected v =
  failwithf "Unknown value '%s' for key %S; expected %s"
    (set_value_to_string v) key expected

let set k v =
  match k, v with
  | "subgoals", Int d when d >= 0 -> subgoal_depth := d
  | "subgoals", Str "on" -> subgoal_depth := 1000
  | "subgoals", Str "off" -> subgoal_depth := 0
  | "subgoals", _ -> set_fail v
                       ~key:"subgoals"
                       ~expected:"'on', 'off', or non-negative integer"

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

let print_theorem name (tys, thm) =
  fprintf !out "\nTheorem %s%s : \n%s.\n%!"
    name (gen_to_string tys) (metaterm_to_formatted_string thm)

let show name =
  print_theorem name (get_generic_lemma name)

let handle_search_witness w =
  if !witnesses then
    fprintf !out "Witness: %s\n%!" (witness_to_string w)

let term_witness (t, w) =
  if !witnesses then
    fprintf !out "Witness: %s\n%!" (witness_to_string w)

let suppress_proof_state_display = State.rref false

type processing_state =
  | Process_top
  | Process_proof of string * (unit -> unit)

let current_state = State.rref Process_top

let rec process1 () =
  State.Undo.push () ;
  try begin match !current_state with
    | Process_top -> process_top1 ()
    | Process_proof (name, compile) -> begin
        try process_proof1 name with
        | Prover.End_proof reason -> begin
            fprintf !out "Proof %s.\n%!" begin
              match reason with
              | `completed ->
                  compile () ;
                  "completed"
              | `aborted -> "ABORTED"
            end ;
            reset_prover () ;
            current_state := Process_top
          end
      end
  end with
  | Failure "lexing: empty token" ->
      if !annotate then fprintf !out "</pre>\n" ;
      exit (if !interactive then 0 else 1)
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
            fprintf !out "Proof NOT completed.\n</pre>\n%!" ;
            exit 1
      end
  | e ->
      State.Undo.undo () ;
      eprintf "Error: %s\n%s%!" (Printexc.to_string e) (Printexc.get_backtrace ()) ;
      interactive_or_exit ()

and process_proof1 name =
  if not !suppress_proof_state_display then display !out ;
  suppress_proof_state_display := false ;
  fprintf !out "%s < %!" name ;
  let input = Parser.command Lexer.token !lexbuf in
  if not !interactive then begin
    let pre, post = if !annotate then "<b>", "</b>" else "", "" in
    fprintf !out "%s%s.%s\n%!" pre (command_to_string input) post
  end ;
  begin match input with
  | Induction(args, hn)    -> induction ?name:hn args
  | CoInduction hn         -> coinduction ?name:hn ()
  | Apply(h, args, ws, hn) -> apply ?name:hn h args ws ~term_witness
  | Backchain(h, ws)       -> backchain h ws ~term_witness
  | Cut(h, arg, hn)        -> cut ?name:hn h arg
  | CutFrom(h, arg, t, hn) -> cut_from ?name:hn h arg t
  | SearchCut(h, hn)       -> search_cut ?name:hn h
  | Inst(h, ws, hn)        -> inst ?name:hn h ws
  | Case(str, hn)          -> case ?name:hn str
  | Assert(t, hn)          ->
      untyped_ensure_no_restrictions t ;
      assert_hyp ?name:hn t
  | Exists(_, t)           -> exists t
  | Monotone(h, t)         -> monotone h t
  | Clear(hs)              -> clear hs
  | Abbrev(h, s)           -> abbrev h s
  | Unabbrev(hs)           -> unabbrev hs
  | Rename(hfr, hto)       -> rename hfr hto
  | Search(bounds) -> begin
      let limit = match bounds with
        | `depth n -> Some n
        | _ -> None
      in
      let witness = match bounds with
        | `witness w -> w
        | _ -> WMagic
      in
      search ~limit ~interactive:!interactive ~witness ~handle_witness:handle_search_witness ()
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
  end ;

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
      current_state := Process_proof (name, fun () ->
          compile (CTheorem(name, tys, thm)) ;
          add_lemma name tys thm
        ) ;
  | SSplit(name, names) ->
      let gen_thms = create_split_theorems name names in
      List.iter begin fun (n, (tys, t)) ->
        print_theorem n (tys, t) ;
        add_lemma n tys t ;
        compile (CTheorem(n, tys, t))
      end gen_thms ;
  | Define(flav, idtys, udefs) ->
      let ids = List.map fst idtys in
      check_noredef ids;
      let (local_sr, local_sign) = locally_add_global_consts idtys in
      let defs = type_udefs ~sr:local_sr ~sign:local_sign udefs |>
                 List.map (fun (head, body) -> {head ; body}) in
      check_def_clauses ids defs ;
      commit_global_consts local_sr local_sign ;
      compile (CDefine(flav, idtys, defs)) ;
      add_defs ids flav defs
  | Schema sch ->
      ignore (Schemas.register_schema sch)
  | TopCommon(Back) ->
      if !interactive then State.Undo.back 2
      else failwith "Cannot use interactive commands in non-interactive mode"
  | TopCommon(Reset) ->
      if !interactive then State.Undo.reset ()
      else failwith "Cannot use interactive commands in non-interactive mode"
  | TopCommon(Set(k, v)) -> set k v
  | TopCommon(Show(n)) -> show n
  | TopCommon(Quit) -> raise End_of_file
  | Import(filename) ->
      compile (CImport filename) ;
      import filename ;
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

let usage_message = "abella [options] <theorem-file>"

let set_output filename =
  out := open_out filename

let set_compile_out filename =
  compile_out := Some (open_out_bin filename)

let makefile = ref false

let options =
  Arg.align
    [
      ("-i", Arg.Set switch_to_interactive,
       " Switch to interactive mode after reading inputs") ;
      ("-o", Arg.String set_output,
       "<file-name> Output to file") ;
      ("-c", Arg.String set_compile_out,
       "<file-name> Compile definitions and theorems in an importable format") ;
      ("-a", Arg.Set annotate, " Annotate mode") ;
      ("-M", Arg.Set makefile, " Output dependencies in Makefile format")
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
    (Sys.Signal_handle (fun _ -> failwith "Interrupted (use ctrl-D to quit)")) ;

  Arg.parse options add_input usage_message ;

  if not !Sys.interactive then
    if !makefile then begin
      List.iter Depend.print_deps !input_files ;
    end else begin
      set_input () ;
      fprintf !out "%s%!" welcome_msg ;
      State.Undo.set_enabled !interactive ;
      while true do number process1 () done
    end
;;
