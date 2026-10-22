(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2026 Inria (Institut National de Recherche            *)
(*                         en Informatique et en Automatique)               *)
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

module Setup = struct
  let compiled : (module Source.THM) option ref = ref None
  let mode : [`batch | `interactive | `switch] ref = ref `interactive
  let annotate : bool ref = ref true
  let recurse : bool ref = ref false
  let input : string ref = ref "" (* file name including suffix *)
  let lexbuf : Lexing.lexbuf ref =
    ref (Lexing.from_string "")
  let unfinished : string list ref = ref []
  let import_mode : [`thc | `source | `auto] ref = ref `thc
  let trust_compiled : bool ref = ref false
end

let on_import : (string -> unit) option ref = ref None

let can_read_specification = State.rref true

let is_interactive () =
  match !Setup.mode with
  | `interactive | `switch -> true
  | _ -> false

let witnesses = State.rref false

exception UserInterrupt
exception AbellaExit of int

(* Input *)

let perform_switch_to_interactive () =
  assert (!Setup.mode = `switch) ;
  Setup.input := "" ;
  Setup.lexbuf := Lexing.from_channel ~with_positions:false stdin ;
  Setup.mode := `interactive ;
  Output.(dest := Channel stdout) ;
  Output.msg_printf "Switching to interactive mode." ;
  State.Undo.undo ()

let interactive_or_exit () =
  match !Setup.mode with
  | `interactive -> ()
  | `switch -> perform_switch_to_interactive ()
  | _ -> raise @@ AbellaExit 1

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
  Output.msg_printf "Typing error%s." (position_range pos) ;
  match ct with
  | CArg ->
      Output.msg_printf ~severity:Error
        "Expression has type %s but is used here with type %s."
        (ty_to_string act) (ty_to_string exp)
  | CFun ->
      Output.msg_printf ~severity:Error
        "Expression is applied to too many arguments"

let teyjus_only_keywords =
  ["closed"; "exportdef"; "import"; "infix"; "infixl"; "infixr"; "local";
   "localkind"; "postfix"; "posfixl"; "prefix"; "prefixr"; "typeabbrev";
   "use_sig"; "useonly"; "sigma"]

let warn_on_teyjus_only_keywords (ktable, ctable) =
  let tokens = List.unique (List.map fst ktable @ List.map fst ctable) in
  let used_keywords = List.intersect tokens teyjus_only_keywords in
  if used_keywords <> [] then
    Output.msg_printf
      "Warning: The following tokens are keywords in Teyjus: %s."
      (String.concat ", " used_keywords)

let update_subordination_sign sr sign =
  List.fold_left Subordination.update sr (sign_to_tys sign)

let read_specification name =
  clear_specification_cache () ;
  if !Setup.mode = `interactive then
    Output.msg_printf "Reading specification %S." name ;
  let read_sign = get_sign name in
  let () = warn_on_teyjus_only_keywords read_sign in
  let sign' = merge_signs [!sign; read_sign] in
  let sr' = update_subordination_sign !sr read_sign in
  let clauses' = get_clauses ~sr:sr' name in
  (* Any exceptions must have been thrown by now - do actual assignments *)
  sr := sr' ;
  sign := sign' ;
  Prover.add_clauses clauses'

(* Compilation and importing *)

type processing_state =
  | Process_top
  | Process_proof of proof_processor

and proof_processor = {
  thm_id : int ;
  thm : string ;
  compile : (fin -> unit) ;
  reset : (unit -> unit) ;
}

let current_state = State.rref Process_top

let comp_spec_sign = State.rref ([], [])
let comp_spec_clauses = State.rref []
let comp_content = State.rref []

let marshal citem =
  match !Setup.compiled with
  | Some (module Thm) -> Thm.marshal citem
  | None -> ()

let ensure_finalized_specification () =
  if !can_read_specification then begin
    can_read_specification := false ;
    comp_spec_sign := !sign ;
    comp_spec_clauses := !Prover.clauses
  end

let compile citem =
  (* ensure_finalized_specification () ; *)
  comp_content := citem :: !comp_content

let predicates (_ktable, ctable) =
  ctable |>
  List.filter_map begin fun (id, Poly (_, Ty (_, targty))) ->
    if List.mem id [k_member] || targty = oaty then None
    else Some id
  end

let write_compilation () =
  match !Setup.compiled with
  | None -> ()
  | Some _ ->
      marshal (Lazy.force Version.self_digest) ;
      marshal Version.version ;
      marshal !comp_spec_sign ;
      marshal !comp_spec_clauses ;
      marshal (predicates !sign) ;
      marshal (List.rev !comp_content) ;
      begin match !Setup.compiled with
      | Some (module Thm) -> Thm.close ()
      | None -> () end

let thc_digest_placeholder () = Digest.string Version.version

let marshal_bytes (values : Obj.t list) =
  let buf = Buffer.create 4096 in
  List.iter (fun v -> Buffer.add_string buf (Marshal.to_string v [])) values ;
  Buffer.contents buf

let marshal_reader (s : string) : unit -> 'a =
  let buf = Bytes.unsafe_of_string s in
  let pos = ref 0 in
  fun () ->
    let v = Marshal.from_string s !pos in
    pos := !pos + Marshal.total_size buf !pos ;
    v

let clause_eq (_,c1) (_,c2) = eq c1 c2

let clauses_to_predicates clauses =
  let clauses = List.map snd clauses in
  clauses |>
  List.map clausify |>
  List.concat |>
  List.map (fun (_, h, _) -> term_head_name h) |>
  List.unique

let ensure_valid_import imp_spec_sign imp_spec_clauses imp_predicates =
  let (ktable, ctable) = !sign in
  let (imp_ktable, imp_ctable) = imp_spec_sign in
  let imp_ctable = List.filter begin
      fun (_id, ty) ->
        match ty with
        | Typing.Poly (_, Ty (_, aty)) when aty = propaty -> false
        | _ -> true
    end imp_ctable in

  (* 1. Imported ktable must be a subset of ktable *)
  let missing_types = List.minus imp_ktable ktable in
  let () = if missing_types <> [] then
      failwithf "Imported file makes reference to unknown types: %s"
        (String.concat ", " (List.map fst missing_types))
  in

  (* 2. Imported ctable must be a subset of ctable *)
  let missing_consts = List.minus imp_ctable ctable in
  let () = if missing_consts <> [] then
      failwithf "Imported file makes reference to unknown constants: %s"
        (String.concat ", " (List.map fst missing_consts))
  in

  (* 3. Imported clauses must be a subset of clauses *)
  let missing_clauses =
    List.minus ~cmp:clause_eq imp_spec_clauses !Prover.clauses
  in
  let () = if missing_clauses <> [] then
      failwithf "Imported file makes reference to unknown clauses for: %s"
        (String.concat ", " (clauses_to_predicates missing_clauses))
  in

  (* 4. Clauses for imported predicates must be subset of imported clauses *)
  let extended_clauses =
    List.minus ~cmp:clause_eq
      (List.find_all
         (fun (_,clause) ->
            clausify clause |>
            List.map (fun (_, h, _) -> term_head_name h) |>
            List.exists (fun h -> List.mem h imp_predicates))
         !Prover.clauses)
      imp_spec_clauses
  in
  let () = if extended_clauses <> [] then
      failwithf "Cannot import file since clauses have been extended for: %s"
        (String.concat ", " (clauses_to_predicates extended_clauses))
  in
  ()


let imported = State.rref []

module Replacement = struct
  type target = {
    name : id ;
    term : term ;
    ty : ty ;
  }

  type t = {
    map : target Itab.t ;
    range : Iset.t ;
  }

  let make withs =
    let map = ref Itab.empty in
    let range = ref Iset.empty in
    List.iter begin fun (decl, defn) ->
      let pred = UCon (ghost_pos, defn, Term.fresh_tyvar ()) in
      let pred = type_uterm ~sr:!sr ~sign:!sign ~ctx:[] pred in
      map := Itab.add decl { name = defn ; term = pred ; ty = tc [] pred } !map ;
      range := Iset.add defn !range
    end withs ;
    if Itab.cardinal !map <> Iset.cardinal !range ||
       Itab.cardinal !map <> List.length withs then
      failwithf "Replacements for \"with\" are not pairwise distrinct" ;
    { map = !map ; range = !range }

  let find repl decl = Itab.find decl repl.map
  (* let find_opt repl decl = Itab.find_opt decl repl.map *)

  let term (repl : t) body =
    let (abs, args) = Itab.fold begin fun decl defn (abs, args) ->
        (Term.abstract decl defn.ty abs, defn.term :: args)
      end repl.map (body, []) in
    Term.app abs args

  let metaterm repl body = map_terms (term repl) body

  let clause repl cl =
    let head = metaterm repl cl.head in
    let body = metaterm repl cl.body in
    { head ; body }

  open struct
    let rec check_no_existing ~what ~mem ids =
      match ids with
      | [] -> ()
      | id :: ids ->
          if mem id then
            failwithf "There is an existing %s named %s" what id ;
          check_no_existing ~what ~mem ids
  end

  let compiled repl comp =
    match comp with
    | CTheorem (nm, tyvars, body, fin) ->
        CTheorem (nm, tyvars, metaterm repl body, fin)
    | CDefine (flav, tyvars, preds, cls) ->
        check_no_existing (List.map fst preds)
          ~what:"defined atom"
          ~mem:(fun id -> Iset.mem id repl.range) ;
        CDefine (flav, tyvars, preds, List.map (clause repl) cls)
    | CImport (fn, ws) ->
        let ws = List.map begin fun (wfrom, wto) ->
            match Itab.find_opt wfrom repl.map with
            | Some defn -> (wfrom, defn.name)
            | _ -> (wfrom, wto)
          end ws in
        CImport (fn, ws)
    | CKind (ids, _) ->
        check_no_existing ids
          ~what:"declared type"
          ~mem:(fun id -> Itab.mem id repl.map) ;
        comp
    | CType (ids, _) ->
        check_no_existing ids
          ~what:"declared constant"
          ~mem:(fun id -> Itab.mem id repl.map) ;
        comp
    | CSuspend _
    | CClose _ -> comp
end

let add_lemma name tys thm =
  match Prover.add_lemma name tys thm with
  | `replace ->
      Output.msg_printf "Warning: overriding existing lemma named %S." name
  | _ -> ()

(* The source-import sandbox needs the prover loop, which is defined
   later; the hook is installed at the end of this module. *)
let process1_hook : (unit -> [`ok | `error]) ref =
  ref (fun () -> `ok)

let initial_snapshot_ref : State.snap option ref = ref None

(* Modules currently being source-compiled, outermost first. *)
let compiling : string list ref = ref []

let json_field name = function
  | `Assoc fields -> begin
      match List.assoc_opt name fields with
      | Some (`String s) -> s
      | _ -> ""
    end
  | _ -> ""

let collected_messages () =
  Output.drain () |>
  List.filter_map begin fun msg ->
    if json_field "type" msg = "system_message" then
      Some (json_field "message" msg)
    else None
  end |>
  String.concat "\n"

let thc_layout sign clauses predicates content =
  marshal_bytes [
    Obj.repr (thc_digest_placeholder ()) ;
    Obj.repr Version.version ;
    Obj.repr sign ;
    Obj.repr clauses ;
    Obj.repr predicates ;
    Obj.repr content ;
  ]

let rec import ~wrt pos impfile withs =
  let filename = Filepath.normalize ~wrt impfile in
  if List.mem filename !imported then
    Output.msg_printf "Ignoring repeated import: %S." filename
  else begin
    Output.msg_printf "Importing: %S." filename ;
    Output.link_message ~pos ~url:(filename ^ ".html") ;
    import_load filename withs
  end

and import_load modname withs =
  let repl = Replacement.make withs in
  if List.mem modname !imported then () else begin
    imported := modname :: !imported ;
    let thm_path = modname ^ ".thm" in
    let module Thm = (val Source.read_thm thm_path) in
    let recursive_invoke () =
      if not !Setup.recurse then
        failwithf "Recursive invocation of Abella prevented (--non-recursive)" ;
      let cmd = Printf.sprintf " %S -o %S" Thm.path Thm.out_path in
      [%trace 1 "Running: abella%s" cmd] ;
      if Sys.command (Sys.executable_name ^ cmd) <> 0 then
        failwithf "Could not create %S" Thm.thc_path
    in
    let use_thc = match !Setup.import_mode with
      | `thc -> true
      | `source -> false
      | `auto -> Source.is_thc_trusted (modname ^ ".thc")
    in
    let bytes =
      if use_thc then begin
        if Thm.is_stale then recursive_invoke () ;
        read_thc ~modname ~recursive_invoke (Thm.thc_contents ())
      end
      else source_compile ~modname
    in
    apply_compiled ~repl ~modname bytes
  end

(* Read and validate the four compiled values, recompiling natively if
   the .thc was produced by a different Abella. Returns the bytes to
   marshal from, which may have changed. *)
and read_thc ~modname ~recursive_invoke bytes =
  let read = marshal_reader bytes in
  let dig = (read () : Digest.t) in
  let ver = (read () : string) in
  if !Setup.trust_compiled || dig = Lazy.force Version.self_digest then bytes
  else begin
    Output.msg_format
      "@[<v2>Warning: The following .thc file was compiled with a different version (%s) of Abella; recompiling@,%s@]"
      ver (modname ^ ".thc") ;
    recursive_invoke () ;
    let module Thm = (val Source.read_thm (modname ^ ".thm")) in
    Thm.thc_contents ()
  end

and apply_compiled ~repl ~modname bytes =
  let read = marshal_reader bytes in
  ignore (read () : Digest.t) ;
  ignore (read () : string) ;
  let imp_spec_sign = (read () : sign) in
  let imp_spec_clauses = (read () : clause list) in
  let imp_predicates = (read () : string list) in
  let imp_content = (read () : compiled list) in
  ensure_valid_import imp_spec_sign imp_spec_clauses imp_predicates ;
  process_decls ~repl ~modname imp_content

and process_decls ~repl ~modname decls =
  match decls with
  | [] -> ()
  | decl :: decls -> begin
      match decl with
      | CTheorem(name, tys, thm, _) ->
          add_lemma name tys thm ;
          process_decls ~repl ~modname decls
      | CDefine(flav, tyargs, idtys, clauses) ->
          let ids = List.map fst idtys in
          check_noredef ids;
          let (basics, consts) = !sign in
          let consts = List.map (fun (id, ty) -> (id, Poly (tyargs, ty))) idtys @ consts in
          sign := (basics, consts) ;
          Prover.add_defs tyargs idtys flav clauses ;
          process_decls ~repl ~modname decls
      | CImport(impname, withs) ->
          import_load (Filepath.normalize ~wrt:modname impname) withs ;
          process_decls ~repl ~modname decls
      | CKind(ids, knd) ->
          check_noredef ids ;
          Prover.add_global_types ids knd;
          process_decls ~repl ~modname decls
      | CType(ids, (Ty(_, aty) as ty)) when aty = propaty-> begin
          let check_types id =
            try begin
              let open Typing in
              let pred = Replacement.find repl id in
              tid_ensure_fully_inferred ~sign:!sign (pred.name, pred.ty) ;
              if ty <> pred.ty then
                failwithf "Expected type %s:%s, got %s:%s"
                  id (ty_to_string ty)
                  pred.name (ty_to_string pred.ty)
            end with Not_found ->
              failwithf "Missing instantiation for %s" id
          in
          List.iter check_types ids ;
          List.map (Replacement.compiled repl) decls |>
          process_decls ~repl ~modname
        end
      | CType(ids,ty) ->
          check_noredef ids ;
          Prover.add_global_consts (List.map (fun id -> (id, ty)) ids) ;
          process_decls ~repl ~modname decls
      | CClose(ty_subords) ->
          List.iter
            (fun (ty, prev) ->
               let curr = Subordination.subordinates !sr ty in
               match List.minus curr prev with
               | [] -> ()
               | xs ->
                   failwithf
                     "Cannot close %s since it is now subordinate to %s"
                     (aty_to_string ty)
                     (String.concat ", " (List.map aty_to_string xs)))
            ty_subords ;
          Prover.close_types !sign !Prover.clauses (List.map fst ty_subords) ;
          process_decls ~repl ~modname decls
      | CSuspend g ->
          Compute.add_guard g ;
          process_decls ~repl ~modname decls
    end

(* Compile an imported module from its source in a pristine sub-session,
   serialize the result in the native .thc layout, then restore the
   parent session. *)
and source_compile ~modname =
  let thm_path = modname ^ ".thm" in
  if List.mem modname !compiling then
    failwithf "Cyclic import of %S: %s"
      modname (String.concat " -> " (List.rev (modname :: !compiling))) ;
  let saved_snapshot = State.snapshot () in
  let saved_mode = !Setup.mode in
  let saved_annotate = !Setup.annotate in
  let saved_recurse = !Setup.recurse in
  let saved_input = !Setup.input in
  let saved_lexbuf = !Setup.lexbuf in
  let saved_compiled = !Setup.compiled in
  let saved_unfinished = !Setup.unfinished in
  let saved_import_mode = !Setup.import_mode in
  let saved_trust_compiled = !Setup.trust_compiled in
  let saved_dest = !Output.dest in
  let saved_undo = State.Undo.is_enabled () in
  let saved_can_read = !can_read_specification in
  let saved_witnesses = !witnesses in
  let saved_state = !current_state in
  let saved_compiling = !compiling in
  let saved_clause_map = !Typing.clause_map in
  let restore () =
    State.reload saved_snapshot ;
    Setup.mode := saved_mode ;
    Setup.annotate := saved_annotate ;
    Setup.recurse := saved_recurse ;
    Setup.input := saved_input ;
    Setup.lexbuf := saved_lexbuf ;
    Setup.compiled := saved_compiled ;
    Setup.unfinished := saved_unfinished ;
    Setup.import_mode := saved_import_mode ;
    Setup.trust_compiled := saved_trust_compiled ;
    Output.dest := saved_dest ;
    State.Undo.set_enabled saved_undo ;
    can_read_specification := saved_can_read ;
    witnesses := saved_witnesses ;
    current_state := saved_state ;
    compiling := saved_compiling ;
    Typing.clause_map := saved_clause_map
  in
  try begin
    State.reload (Option.get !initial_snapshot_ref) ;
    State.Undo.set_enabled false ;
    Setup.mode := `batch ;
    Setup.annotate := false ;
    Setup.recurse := false ;
    Setup.compiled := None ;
    Setup.unfinished := [] ;
    Setup.input := thm_path ;
    let module Src = (val Source.read thm_path) in
    Setup.lexbuf := Src.lex true ;
    compiling := modname :: saved_compiling ;
    Output.collect_mode () ;
    ignore (Output.drain ()) ;
    Option.iter (fun f -> f (Source.canon modname)) !on_import ;
    let rec drive () =
      match !process1_hook () with
      | `ok -> drive ()
      | `error -> raise (AbellaExit 1)
    in
    drive ()
  end with
  | AbellaExit 0 ->
      let spec_sign = !comp_spec_sign in
      let spec_clauses = !comp_spec_clauses in
      let predicates = predicates !sign in
      let content = List.rev !comp_content in
      let bytes = thc_layout spec_sign spec_clauses predicates content in
      ignore (collected_messages ()) ;
      restore () ;
      Source.add_virtual (modname ^ ".thc") bytes ;
      Source.set_thc_trusted (modname ^ ".thc") true ;
      bytes
  | AbellaExit n ->
      let text = collected_messages () in
      restore () ;
      failwithf "Could not compile imported module %S (exit %d)%s%s"
        modname n (if text = "" then "" else ": ") text
  | e ->
      let text = collected_messages () in
      restore () ;
      let msg = match e with
        | Failure msg -> msg
        | _ -> sorry e
      in
      failwithf "Could not compile imported module %S: %s%s"
        modname msg (if text = "" then "" else "\n" ^ text)


(* Proof processing *)

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
  | _ -> assert false

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

  | "witnesses", Str "on" -> witnesses := true
  | "witnesses", Str "off" -> witnesses := false
  | "witnesses", _ -> set_fail v
                        ~key:"witnesses"

  | "load_path", QStr s ->
      Filepath.set_load_path ~wrt:!Setup.input s
  | _, _ -> failwithf "Unknown key '%s'" k

let handle_search_witness w =
  if !witnesses then
    Output.msg_printf "Witness: %s." (witness_to_string w)

let term_witness (_t, w) =
  if !witnesses then
    Output.msg_printf "Witness: %s." (witness_to_string w)

let suppress_proof_state_display = State.rref false

let rec process1 () =
  State.Undo.push () ;
  let outcome = ref `ok in
  (try begin match !current_state with
    | Process_top -> process_top1 ()
    | Process_proof proc -> begin
        try process_proof1 proc with
        | Prover.End_proof reason -> begin
            Output.msg_printf "Proof %s" begin
              match reason with
              | `completed fin -> begin
                  proc.compile fin ;
                  if fin = Unfinished then
                    Setup.unfinished := proc.thm :: !Setup.unfinished ;
                  Printf.sprintf "completed%s"
                    (match fin with
                     | Finished -> ""
                     | Unfinished -> " *** USING skip ***")
                end
              | `aborted -> "ABORTED"
            end ;
            proc.reset () ;
            (* print_clauses () ; *)
            current_state := Process_top
          end
      end
  end with
  | Abella_types.Reported_parse_error ->
      outcome := `error ;
      State.Undo.undo () ;
      Lexing.flush_input !Setup.lexbuf ;
      interactive_or_exit ()
  | Parser.Error ->
      outcome := `error ;
      State.Undo.undo () ;
      Output.msg_printf ~severity:Error
        "Syntax error%s." (position !Setup.lexbuf) ;
      Lexing.flush_input !Setup.lexbuf ;
      interactive_or_exit ()
  | TypeInferenceFailure(exp, act, ci) ->
      outcome := `error ;
      State.Undo.undo () ;
      type_inference_error ci exp act ;
      interactive_or_exit ()
  | End_of_file ->
      write_compilation () ;
      if !Setup.mode = `switch then
        perform_switch_to_interactive ()
      else begin
        match !current_state with
        | Process_top ->
            if not (is_interactive ()) && !Setup.unfinished <> [] then begin
              Output.msg_printf "There were skips in these theorem(s): %s"
                (String.concat ", "  !Setup.unfinished)
            end ;
            Output.flush () ;
            raise @@ AbellaExit 0
        | _ ->
            Output.msg_printf ~severity:Error "Proof NOT Completed." ;
            Output.flush () ;
            raise @@ AbellaExit 1
      end
  | e ->
      State.Undo.undo () ;
      let msg = match e with
        | Failure msg -> msg
        | Unify.UnifyFailure fl -> Unify.explain_failure fl
        | Unify.UnifyError err -> Unify.explain_error err
        | UserInterrupt -> "Interrupted (use Ctrl-D to quit)"
        | _ -> sorry e
      in
      Output.msg_printf ~severity:Error "Error: %s" msg ;
      outcome := `error ;
      interactive_or_exit ()) ;
  !outcome

and process_proof1 proc =
  if !Setup.mode = `interactive && not !suppress_proof_state_display then
    Output.non_annot "%s" @@ Prover.get_display () ;
  suppress_proof_state_display := false ;
  if !Setup.mode = `interactive then
    Output.non_annot "%s < " proc.thm ;
  let input = Parser.command_start Lexer.token !Setup.lexbuf in
  let cmd_string = command_to_string input.el in
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

and process_top1 () =
  if !Setup.mode = `interactive then Output.non_annot "Abella < " ;
  let input = Parser.top_command_start Lexer.token !Setup.lexbuf in
  let cmd_string = top_command_to_string input.el in
  if !Setup.mode <> `interactive then Output.non_annot "%s.\n%!" cmd_string ;
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
  begin match input.el with
  | Theorem(name, tys, thm) -> begin
      let st = get_bind_state () in
      let seq = Prover.copy_sequent () in
      let thm = type_umetaterm ~sr:!sr ~sign:!sign thm in
      check_theorem tys thm ;
      Prover.theorem thm ;
      let oldsign = !sign in
      let thm_compile fin =
        sign := oldsign ;
        compile (CTheorem(name, tys, thm, fin)) ;
        add_lemma name tys thm
      in
      let thm_reset () =
        sign := oldsign ;
        Prover.reset_prover st seq ()
      in
      Prover.start_proof () ;
      current_state := Process_proof {
          thm_id ; thm = name ;
          compile = thm_compile ;
          reset = thm_reset
        }
    end
  | SSplit(name, names) ->
      let gen_thms = Prover.create_split_theorems name names in
      List.iter begin fun (n, (tys, t)) ->
        Output.msg_format "%t" (Prover.print_theorem n (tys, t)) ;
        add_lemma n tys t ;
        compile (CTheorem(n, tys, t, Finished))
      end gen_thms ;
  | Define _ ->
      compile (Prover.register_definition input.el)
  | Suspend (head, test) ->
      let g = Compute.make_guard ~head ~test in
      Compute.add_guard g ;
      compile @@ CSuspend g
  | TopCommon(Back) ->
      if !Setup.mode = `interactive then State.Undo.back 2
      else failwith "Cannot use interactive commands in non-interactive mode"
  | TopCommon(Reset) ->
      if !Setup.mode = `interactive then State.Undo.reset ()
      else failwith "Cannot use interactive commands in non-interactive mode"
  | TopCommon(Set(k, v)) -> set k v
  | TopCommon(Show(n)) -> Output.msg_format "%t" (Prover.show n)
  | TopCommon(Quit) -> raise End_of_file
  | Import(filename, pos, withs) ->
      compile (CImport (filename, withs)) ;
      import ~wrt:!Setup.input pos filename withs
  | Specification(filename, pos) ->
      if !can_read_specification then begin
        let filename = Filepath.normalize ~wrt:!Setup.input filename in
        read_specification filename ;
        ensure_finalized_specification () ;
        if !Setup.annotate then
          Output.link_message ~pos ~url:(filename ^ ".lp.html") ;
      end else
        failwith "Specification can only be read \
                 \ at the begining of a development."
  | Query(q) -> query q
  | Kind(ids,knd) ->
      check_noredef ids;
      Prover.add_global_types ids knd;
      compile (CKind (ids,knd)) ;
  | Type(ids, ty) ->
      check_noredef ids ;
      Prover.add_global_consts (List.map (fun id -> (id, ty)) ids) ;
      compile (CType(ids, ty)) ;
  | Close(atys) ->
      Prover.close_types !sign !Prover.clauses atys ;
      compile (CClose(List.map (fun aty -> (aty, Subordination.subordinates !sr aty)) atys))
  end ;
  if not !Setup.annotate then Output.blank_line ()

let () = process1_hook := process1

let initial_snapshot = State.snapshot ()
let () = initial_snapshot_ref := Some initial_snapshot

let welcome_msg = sprintf "Welcome to Abella %s.\n" Version.version
