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

module Setup = struct
  let compiled : (module Source.THM) option ref = ref None
  let mode : [`batch | `interactive | `switch] ref = ref `interactive
  let annotate : bool ref = ref true
  let recurse : bool ref = ref false
  let input : string ref = ref "" (* file name including suffix *)
  let lexbuf : Lexing.lexbuf ref =
    ref (Lexing.from_string "")
  let unfinished : string list ref = ref []
  let axioms : string list ref = State.rref []
  let import_mode : [`thc | `source | `auto] ref = ref `thc
  let trust_compiled : bool ref = ref false
  let file_kind : [`thm | `thmod] ref = Typing.file_kind
  let thmod_name : string option ref = State.rref None
  let thmod_params : string list ref = State.rref []
  let thmod_finished : bool ref = State.rref false
end

let on_import : (string -> unit) option ref = ref None

let thm_instances : Thmod.instance list ref = State.rref []
let thmod_loading : string list ref = State.rref []

let can_read_specification = State.rref true

let is_interactive () =
  match !Setup.mode with
  | `interactive | `switch -> true
  | _ -> false

let in_module () = Thmod.current_name () <> None

let bound_params () =
  if in_module () then Thmod.all_params () else []

let witnesses = State.rref false

exception UserInterrupt
exception AbellaExit of int

(* Input *)

let perform_switch_to_interactive () =
  assert (!Setup.mode = `switch) ;
  let from_thmod = !Setup.file_kind = `thmod in
  Setup.input := "" ;
  Setup.lexbuf := Lexing.from_channel ~with_positions:false stdin ;
  Setup.mode := `interactive ;
  Output.(dest := Channel stdout) ;
  Output.msg_printf "Switching to interactive mode." ;
  State.Undo.undo () ;
  Setup.file_kind := `thm ;
  Setup.thmod_name := None ;
  Setup.thmod_params := [] ;
  Setup.thmod_finished := false ;
  thmod_loading := [] ;
  if from_thmod then begin
    thm_instances := [] ;
    Thmod.reset ()
  end

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
  if !Setup.file_kind = `thmod || in_module () then
    Thmod.add_compiled citem
  else
    comp_content := citem :: !comp_content

let predicates (_ktable, ctable) =
  ctable |>
  List.filter_map begin fun (id, Poly (_, Ty (_, targty))) ->
    if List.mem id [k_member] || targty = oaty then None
    else Some id
  end

let thmod_sign content =
  let ktable =
    List.flatten_map (function
        | CKind (ids, knd) -> List.map (fun id -> (id, knd)) ids
        | _ -> []) content
  in
  let ctable =
    List.flatten_map (function
        | CType (ids, typarams, ty)
        | CDeclPred (ids, typarams, ty) ->
            List.map (fun id -> (id, Poly (typarams, ty))) ids
        | CDefine (_, typarams, idtys, _) ->
            List.map (fun (id, ty) -> (id, Poly (typarams, ty))) idtys
        | CTheorem _ | CKind _ | CImport _ | CClose _ | CSuspend _ -> [])
      content
  in
  (ktable, ctable)

let write_compilation () =
  match !Setup.compiled with
  | None -> ()
  | Some _ ->
      marshal (Lazy.force Version.self_digest) ;
      marshal Version.version ;
      if !Setup.file_kind = `thmod then begin
        let name = match Thmod.top_name () with
          | Some name -> name
          | None -> failwith "Cannot write a .thmodc without a module"
        in
        marshal name ;
        marshal (Thmod.top_params ())
      end ;
      let content, exported =
        if !Setup.file_kind = `thmod then
          (Thmod.exported_content (), Thmod.exported_names ())
        else
          ([], [])
      in
      let spec_sign =
        if !Setup.file_kind = `thmod then thmod_sign content
        else !comp_spec_sign
      in
      marshal spec_sign ;
      marshal !comp_spec_clauses ;
      if !Setup.file_kind = `thmod then begin
        let preds =
          predicates !sign |> List.filter (fun id -> List.mem id exported)
        in
        marshal preds ;
        marshal content
      end else begin
        marshal (predicates !sign) ;
        marshal (List.rev !comp_content)
      end ;
      if !Setup.file_kind = `thmod then begin
        marshal (Thmod.nested_module_names ()) ;  (* nested modules *)
        marshal (Thmod.exported_names ()) ;       (* exported names *)
      end ;
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

  let metaterm repl body =
    let alist =
      Itab.fold (fun decl defn alist -> (decl, defn.term) :: alist)
        repl.map []
    in
    replace_metaterm_vars alist body

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
    | CType (ids, _, _)
    | CDeclPred (ids, _, _) ->
        check_no_existing ids
          ~what:"declared constant"
          ~mem:(fun id -> Itab.mem id repl.map) ;
        comp
    | CSuspend _
    | CClose _ -> comp
end

let add_lemma ?(fin=Finished) name tys thm =
  match Prover.add_lemma ~fin name tys thm with
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

let thmodc_layout name params sign clauses predicates content nested exports =
  marshal_bytes [
    Obj.repr (thc_digest_placeholder ()) ;
    Obj.repr Version.version ;
    Obj.repr name ;
    Obj.repr params ;
    Obj.repr sign ;
    Obj.repr clauses ;
    Obj.repr predicates ;
    Obj.repr content ;
    Obj.repr nested ;
    Obj.repr exports ;
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
      | CTheorem(name, tys, thm, fin) ->
          if fin = Axiomatic then
            Setup.axioms := name :: !Setup.axioms ;
          add_lemma ~fin name tys thm ;
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
      | CType(ids, _, (Ty(_, aty) as ty)) when aty = propaty-> begin
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
      | CType(ids, typarams, ty)
      | CDeclPred(ids, typarams, ty) ->
          check_noredef ids ;
          Prover.add_global_consts ~typarams
            (List.map (fun id -> (id, ty)) ids) ;
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
  let saved_file_kind = !Setup.file_kind in
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
    Setup.file_kind := saved_file_kind ;
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
    Setup.file_kind := `thm ;
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
      Source.add_virtual_thc (modname ^ ".thc") bytes ;
      if Source.virtual_exists (modname ^ ".thc") then
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


(* Compile a virtual .thmod in a pristine sub-session and install its
   .thmodc bytes in the virtual file system. *)
let source_compile_thmod ~modname =
  let thmod_path = modname ^ ".thmod" in
  let compiling_key = modname ^ ".thmod" in
  if List.mem compiling_key !compiling then
    failwithf "Cyclic import of %S: %s"
      thmod_path
      (String.concat " -> " (List.rev (compiling_key :: !compiling))) ;
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
  let saved_file_kind = !Setup.file_kind in
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
    Setup.file_kind := saved_file_kind ;
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
    Thmod.reset () ;
    State.Undo.set_enabled false ;
    Setup.mode := `batch ;
    Setup.annotate := false ;
    Setup.recurse := false ;
    Setup.compiled := None ;
    Setup.unfinished := [] ;
    Setup.input := thmod_path ;
    Setup.file_kind := `thmod ;
    Setup.thmod_name := None ;
    Setup.thmod_params := [] ;
    Setup.thmod_finished := false ;
    let module Src = (val Source.read_thmod thmod_path) in
    Setup.lexbuf := Src.lex true ;
    compiling := compiling_key :: saved_compiling ;
    Output.collect_mode () ;
    ignore (Output.drain ()) ;
    Option.iter (fun f -> f (Source.canon thmod_path)) !on_import ;
    let rec drive () =
      match !process1_hook () with
      | `ok -> drive ()
      | `error -> raise (AbellaExit 1)
    in
    drive ()
  end with
  | AbellaExit 0 ->
      let name = match Thmod.top_name () with
        | Some name -> name
        | None -> failwith "A .thmod must contain a top-level module"
      in
      let params = Thmod.top_params () in
      let content = Thmod.exported_content () in
      let nested = Thmod.nested_module_names () in
      let exports = Thmod.exported_names () in
      let artifact_sign = thmod_sign content in
      let preds =
        predicates artifact_sign |> List.filter (fun id -> List.mem id exports)
      in
      let bytes =
        thmodc_layout name params artifact_sign !comp_spec_clauses preds
          content nested exports
      in
      ignore (collected_messages ()) ;
      restore () ;
      Source.add_virtual_thc (modname ^ ".thmodc") bytes ;
      if Source.virtual_exists (modname ^ ".thmodc") then
        Source.set_thc_trusted (modname ^ ".thmodc") true ;
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



type thmod_artifact = {
  ta_name : string ;
  ta_params : string list ;
  ta_content : compiled list ;
  ta_nested : string list ;
  ta_exports : string list ;
}

type pred_value = {
  pv_name : string ;
  pv_typarams : string list ;
  pv_ty : ty ;
}

type axiom_value = {
  av_name : string ;
  av_typarams : string list ;
  av_stmt : metaterm ;
  av_tag : fin ;
}

type import_value =
  | PredValue of pred_value
  | AxiomValue of axiom_value

type import_target =
  | TargetTemplate of Thmod.template
  | TargetInstance of Thmod.instance

type resolved_key = {
  rk_source : string ;
  rk_prefixed : string ;
  rk_predicate : bool ;
}

let is_predicate_ty ty =
  match observe_ty ty with
  | Ty (_, aty) -> aty = propaty

let parse_thmod_artifact bytes =
  let read = marshal_reader bytes in
  ignore (read () : Digest.t) ;
  ignore (read () : string) ;
  let name = (read () : string) in
  let params = (read () : string list) in
  ignore (read () : sign) ;
  ignore (read () : clause list) ;
  ignore (read () : string list) ;
  let content = (read () : compiled list) in
  let nested = (read () : string list) in
  let exports = (read () : string list) in
  { ta_name = name ;
    ta_params = params ;
    ta_content = content ;
    ta_nested = nested ;
    ta_exports = exports ;
  }

let recompile_thmod ~path ~out_path =
  if not !Setup.recurse then
    failwithf "Recursive invocation of Abella prevented (--non-recursive)" ;
  let cmd = Printf.sprintf " %S -o %S" path out_path in
  [%trace 1 "Running: abella%s" cmd] ;
  if Sys.command (Sys.executable_name ^ cmd) <> 0 then
    failwithf "Could not create the compiled form of %S" path

let load_thmod_artifact ~modname =
  let path = modname ^ ".thmod" in
  let canonical = Source.canon path in
  if List.mem canonical !thmod_loading then
    failwithf "Cyclic import of %S: %s"
      path (String.concat " -> " (List.rev (canonical :: !thmod_loading))) ;
  let saved_loading = !thmod_loading in
  thmod_loading := canonical :: saved_loading ;
  Fun.protect ~finally:(fun () -> thmod_loading := saved_loading)
    begin fun () ->
      let module Src = (val Source.read_thmod path) in
      let recursive_invoke () =
        recompile_thmod ~path:Src.path ~out_path:Src.out_path
      in
      let use_artifact = match !Setup.import_mode with
        | `thc -> true
        | `source -> false
        | `auto -> Source.is_thc_trusted Src.thc_path
      in
      if Source.virtual_exists path then begin
        if not use_artifact || Src.is_stale then
          ignore (source_compile_thmod ~modname)
      end else if not use_artifact || Src.is_stale then
        recursive_invoke () ;
      let bytes = Src.thc_contents () in
      let read_digest bytes =
        let read = marshal_reader bytes in
        let digest = (read () : Digest.t) in
        let version = (read () : string) in
        (digest, version)
      in
      let digest, version = read_digest bytes in
      if not !Setup.trust_compiled &&
         digest <> Lazy.force Version.self_digest then begin
        Output.msg_format
          ("@[<v2>Warning: The following .thmodc file was compiled with a "
           ^^ "different version (%s) of Abella; recompiling@,%s@]")
          version (modname ^ ".thmodc") ;
        recursive_invoke () ;
        parse_thmod_artifact (Src.thc_contents ())
      end else
        parse_thmod_artifact bytes
    end

let find_thm_instance name =
  List.find_some begin fun inst ->
    if inst.Thmod.ins_name = name then Some inst else None
  end !thm_instances

let find_import_instance name =
  if in_module () then Thmod.find_instance name
  else find_thm_instance name

let add_import_instance inst =
  if in_module () then Thmod.add_instance inst
  else begin
    if find_thm_instance inst.Thmod.ins_name <> None then
      failwithf "Module name %s is already imported" inst.Thmod.ins_name ;
    thm_instances := !thm_instances @ [inst]
  end

let import_prefix name =
  if in_module () then Thmod.instance_prefix name else [name]

let resolve_import_target mi =
  match mi.mi_source with
  | QuoteSource (file, _) ->
      if Filename.check_suffix file ".thmod" then
        failwith "Do not include the .thmod extension in an import" ;
      let file = Filepath.normalize ~wrt:!Setup.input file in
      let artifact = load_thmod_artifact ~modname:file in
      let base = Filename.basename file in
      if artifact.ta_name <> base then
        failwithf "Module %s does not match the file name %s.thmod"
          artifact.ta_name base ;
      let source = Source.canon (file ^ ".thmod") in
      let template = {
        Thmod.tp_name = artifact.ta_name ;
        tp_from = [] ;
        tp_source = source ;
        tp_params = artifact.ta_params ;
        tp_content = artifact.ta_content ;
        tp_nested = artifact.ta_nested ;
      } in
      (TargetTemplate template, artifact.ta_name, source)
  | NameSource name ->
      let template = Thmod.find_template name in
      let instance = find_import_instance name in
      if mi.mi_tyargs <> [] then
        begin match template with
        | Some template ->
            (TargetTemplate template, name, template.Thmod.tp_source)
        | None ->
            begin match instance with
            | Some _ ->
                failwithf "Module %s is already instantiated" name
            | None ->
                failwithf "Unknown module template %s with type arguments" name
            end
        end
      else
        begin match instance with
        | Some instance ->
            (TargetInstance instance, name, instance.Thmod.ins_source)
        | None ->
            begin match template with
            | Some template ->
                (TargetTemplate template, name, template.Thmod.tp_source)
            | None -> failwithf "Unknown module %s" name
            end
        end

let resolve_type_args args =
  List.map begin fun ty ->
    let ty = if in_module () then Thmod.resolve_ty ty else ty in
    kind_check !sign ty ;
    if contains_prop ty then
      failwithf "Type argument %s may not contain prop"
        (ty_to_string ty) ;
    let free = get_typaram ty in
    if in_module () then begin
      let allowed = Thmod.all_params () in
      match List.minus free allowed with
      | [] -> ()
      | bad :: _ ->
          failwithf "Type argument %s contains the free type variable %s"
            (ty_to_string ty) bad
    end else if free <> [] then
      failwithf "Type argument %s contains a free type variable"
        (ty_to_string ty) ;
    ty
  end args

let target_index decls from =
  List.flatten_map begin fun decl ->
    List.filter_map begin fun id ->
      match Thmod_import.strip_path from id with
      | Some relative -> Some (relative, id, decl)
      | None -> None
    end (Thmod_import.ids_of_compiled decl)
  end decls

let find_decl_by_id id decls =
  List.find_some begin fun decl ->
    if List.mem id (Thmod_import.ids_of_compiled decl) then Some decl
    else None
  end decls

let materialize_import ~decls ~from ~to_ ~params ~args ~is_instance ~avoid =
  let renamer =
    if is_instance then
      Thmod_import.prefix_renamer ~from ~to_
        ~const_ids:[] ~kind_ids:[] ~lemma_ids:[] ()
    else
      Thmod_import.prefix_renamer ~from ~to_
        ~const_ids:(Thmod_import.const_ids decls)
        ~kind_ids:(Thmod_import.kind_ids decls)
        ~lemma_ids:(Thmod_import.lemma_ids decls) ()
  in
  let tysub =
    if is_instance then [] else Thmod_import.tyvar_subst params args
  in
  let avoid = avoid @ List.flatten_map get_typaram args in
  let materialized =
    List.map
      (Thmod_import.materialize_decl ~renamer ~avoid ~tysub)
      decls
  in
  let rigid_decls =
    if is_instance then decls
    else List.map (Thmod_import.map_compiled renamer) decls
  in
  let rigid = Thmod.rigid_predicates_of_decls rigid_decls in
  (renamer, materialized, rigid)

let value_of_item item =
  match item.Thmod.item_class with
  | Thmod.PredicateItem | Thmod.DefineItem ->
      begin match item.Thmod.item_ty with
      | Some ty ->
          PredValue {
            pv_name = item.Thmod.item_name ;
            pv_typarams = item.Thmod.item_typarams ;
            pv_ty = ty ;
          }
      | None -> failwithf "Missing type for predicate %s"
                  item.Thmod.item_name
      end
  | Thmod.AxiomItem | Thmod.TheoremItem ->
      let (tys, stmt) = Prover.get_generic_lemma item.Thmod.item_name in
      let tag = Prover.get_lemma_tag item.Thmod.item_name in
      AxiomValue {
        av_name = item.Thmod.item_name ;
        av_typarams = tys ;
        av_stmt = stmt ;
        av_tag = tag ;
      }
  | Thmod.KindItem | Thmod.TypeItem ->
      failwithf "%s is not a predicate or axiom"
        item.Thmod.item_name

let value_of_name ~predicate name =
  let local_name () =
    let name = Thmod.resolve_id name in
    match Thmod.lookup_item_by_name name with
    | Some item -> Some (name, value_of_item item)
    | None -> None
  in
  let value =
    if in_module () then
      match local_name () with
      | Some (_, value) -> Some value
      | None -> None
    else None
  in
  match value with
  | Some value -> value
  | None ->
      if predicate then
        begin match List.assoc_opt name (snd !sign) with
        | Some (Poly (typarams, ty)) when is_predicate_ty ty ->
            PredValue {
              pv_name = name ;
              pv_typarams = typarams ;
              pv_ty = ty ;
            }
        | _ -> failwithf "%s is not a declared or defined predicate" name
        end
      else
        begin
          try
            let (tys, stmt) = Prover.get_generic_lemma name in
            let tag = Prover.get_lemma_tag name in
            AxiomValue {
              av_name = name ;
              av_typarams = tys ;
              av_stmt = stmt ;
              av_tag = tag ;
            }
          with _ -> failwithf "%s is not an axiom or theorem" name
        end

let resolve_with_keys ~materialized ~decls ~from ~renamer withs =
  let index = target_index decls from in
  let seen = ref [] in
  List.map begin fun (key, value) ->
    let key = qualid_to_string key in
    if List.mem key !seen then
      failwithf "Duplicate with key %s" key ;
    seen := key :: !seen ;
    let candidates =
      List.filter (fun (relative, _, _) -> relative = key) index
    in
    match candidates with
    | [] -> failwithf "Unknown with key %s" key
    | (_, source_id, decl) :: rest ->
        if List.exists (fun (_, id, _) -> id <> source_id) rest then
          failwithf "Ambiguous with key %s" key ;
        let predicate =
          match Thmod.class_of_compiled decl with
          | Some Thmod.PredicateItem -> true
          | Some Thmod.AxiomItem -> false
          | _ ->
              failwithf "%s is not a declared predicate or axiom" key
        in
        let prefixed =
          if predicate then renamer.Thmod_import.r_const source_id
          else renamer.Thmod_import.r_lemma source_id
        in
        if predicate then begin
          match find_decl_by_id prefixed materialized with
          | Some (CDeclPred (_, _, ty) | CType (_, _, ty)) ->
              if contains_prop_argument ty then
                failwithf
                  "Declared predicate %s is higher-order and cannot be a key"
                  key
          | _ -> failwithf "Cannot classify with key %s" key
        end ;
        ({ rk_source = source_id ;
           rk_prefixed = prefixed ;
           rk_predicate = predicate ;
         }, value)
  end withs

let target_local_names ~renamer decls =
  let consts =
    List.flatten_map (function
        | CType (ids, _, _) | CDeclPred (ids, _, _) -> ids
        | CDefine (_, _, idtys, _) -> List.map fst idtys
        | CTheorem _ | CKind _ | CImport _ | CClose _ | CSuspend _ -> [])
      decls
    |> List.map renamer.Thmod_import.r_const
  in
  let kinds =
    List.flatten_map (function
        | CKind (ids, _) -> ids
        | _ -> [])
      decls
    |> List.map renamer.Thmod_import.r_tycons
  in
  (List.unique consts, List.unique kinds)

let replay_imported_decls decls =
  let update_metaterm_subordination mt =
    ignore begin
      Metaterm.map_on_tys (fun ty ->
          sr := Subordination.update !sr ty ; ty)
        mt
    end
  in
  let record decl =
    if !Setup.file_kind = `thmod || in_module () then
      Thmod.add_imported_compiled decl
    else
      compile decl
  in
  let rec replay = function
    | [] -> ()
    | decl :: rest ->
        begin match decl with
        | CTheorem (name, tys, stmt, fin) ->
            update_metaterm_subordination stmt ;
            if fin = Axiomatic then
              Setup.axioms := name :: !Setup.axioms ;
            add_lemma ~fin name tys stmt
        | CDefine (flavor, typarams, idtys, clauses) ->
            check_noredef (List.map fst idtys) ;
            List.iter (fun (_, ty) -> sr := Subordination.update !sr ty)
              idtys ;
            List.iter begin fun cl ->
              update_metaterm_subordination cl.head ;
              update_metaterm_subordination cl.body
            end clauses ;
            Checks.ensure_no_schm_clauses typarams clauses ;
            let (basics, consts) = !sign in
            let consts =
              List.map (fun (id, ty) -> (id, Poly (typarams, ty))) idtys
              @ consts
            in
            sign := (basics, consts) ;
            Prover.add_defs ~strat_errors:true typarams idtys flavor clauses
        | CKind (ids, knd) ->
            check_noredef ids ;
            Prover.add_global_types ids knd
        | CType (ids, typarams, ty)
        | CDeclPred (ids, typarams, ty) ->
            check_noredef ids ;
            Prover.add_global_consts ~typarams
              (List.map (fun id -> (id, ty)) ids)
        | CImport _ ->
            failwith "Unexpected import in a compiled reasoning module"
        | CClose _ | CSuspend _ ->
            failwith "Unexpected command in a compiled reasoning module"
        end ;
        record decl ;
        replay rest
  in
  replay decls

let import_module mi =
  let target, default_name, source = resolve_import_target mi in
  let name = match mi.mi_alias with
    | Some alias -> alias
    | None -> default_name
  in
  if List.mem name (Thmod.all_params ()) then
    failwithf "Module name %s is already used as a module parameter" name ;
  begin match mi.mi_alias with
  | None ->
      if find_import_instance name <> None then
        failwithf "Module %s has already been imported" name
  | Some alias ->
      if find_import_instance alias <> None then
        failwithf "Module name %s is already imported" alias ;
      if Thmod.find_template alias <> None then
        failwithf "Module name %s is already in use" alias
  end ;
  let prefix = import_prefix name in
  let source_decls, from, params, args, is_instance =
    match target with
    | TargetTemplate template ->
        let args = resolve_type_args mi.mi_tyargs in
        if List.length args <> List.length template.Thmod.tp_params then
          failwithf "Module %s expects %d type arguments but got %d"
            template.Thmod.tp_name
            (List.length template.Thmod.tp_params)
            (List.length args) ;
        (template.Thmod.tp_content, template.Thmod.tp_from,
         template.Thmod.tp_params, args, false)
    | TargetInstance instance ->
        if mi.mi_tyargs <> [] then
          failwithf "Module %s is already instantiated"
            instance.Thmod.ins_name ;
        (instance.Thmod.ins_decls, instance.Thmod.ins_prefix,
         [], [], true)
  in
  let args =
    match target with
    | TargetTemplate _ -> args
    | TargetInstance instance -> instance.Thmod.ins_tyargs
  in
  let renamer, materialized, rigid =
    materialize_import ~decls:source_decls ~from ~to_:prefix
      ~params ~args ~is_instance ~avoid:(bound_params ())
  in
  let existing_instances =
    if in_module () then Thmod.all_instances () else !thm_instances
  in
  let rigid =
    List.fold_left begin fun rigid instance ->
      if instance.Thmod.ins_source = source then
        Iset.union rigid
          (Thmod.rigid_predicates_of_decls instance.Thmod.ins_decls)
      else
        rigid
    end rigid existing_instances
  in
  let keys =
    resolve_with_keys ~materialized ~decls:source_decls ~from ~renamer
      mi.mi_withs
  in
  let resolved =
    List.map begin fun (key, value_name) ->
      let value_name = qualid_to_string value_name in
      let value =
        value_of_name ~predicate:key.rk_predicate value_name
      in
      begin match key.rk_predicate, value with
      | true, PredValue _ -> ()
      | false, AxiomValue axiom when axiom.av_tag = Unfinished ->
          failwithf
            "Axiom key %s cannot use the unfinished theorem %s"
            key.rk_source axiom.av_name
      | false, AxiomValue _ -> ()
      | true, AxiomValue _ ->
          failwithf "Predicate key %s requires a predicate value" key.rk_source
      | false, PredValue _ ->
          failwithf "Axiom key %s requires an axiom or theorem value"
            key.rk_source
      end ;
      (key, value)
    end keys
  in
  let pred_pairs =
    List.filter_map begin fun (key, value) ->
      match value with
      | PredValue value -> Some (key, value)
      | AxiomValue _ -> None
    end resolved
  in
  let axiom_pairs =
    List.filter_map begin fun (key, value) ->
      match value with
      | AxiomValue value -> Some (key, value)
      | PredValue _ -> None
    end resolved
  in
  let pred_names = List.map (fun (_, v) -> v.pv_name) pred_pairs in
  if not (List.is_unique pred_names) then
    failwith "Predicate values in with clauses must be pairwise distinct" ;
  List.iter begin fun (key, value) ->
    if Term.Iset.mem value.pv_name rigid then
      failwithf
        "Predicate value %s already occurs in the declarations of %s"
        value.pv_name key.rk_source
  end pred_pairs ;
  let pred_map =
    List.map (fun (key, value) -> (key.rk_prefixed, value.pv_name))
      pred_pairs
  in
  let substitute name =
    match List.assoc_opt name pred_map with
    | Some name -> name
    | None -> name
  in
  let target_consts, target_kinds =
    target_local_names ~renamer source_decls
  in
  List.iter begin fun (key, _) ->
    match find_decl_by_id key.rk_prefixed materialized with
    | Some (CDeclPred (_, _, ty) | CType (_, _, ty)) ->
        begin match
            List.intersect (Thmod_import.tycons_of_ty ty) target_kinds
        with
        | [] -> ()
        | name :: _ ->
            failwithf
              "Predicate key %s mentions the target-local type %s"
              key.rk_source name
        end
    | _ -> failwithf "Cannot classify predicate key %s" key.rk_source
  end pred_pairs ;
  List.iter begin fun (key, _) ->
    match find_decl_by_id key.rk_prefixed materialized with
    | Some (CTheorem (_, _, stmt, _)) ->
        let stmt = Thmod_import.map_metaterm_constants substitute stmt in
        begin match
            List.intersect
              (Thmod_import.metaterm_names stmt)
              (target_consts @ target_kinds)
        with
        | [] -> ()
        | name :: _ ->
            failwithf
              "Axiom key %s mentions the target-local name %s"
              key.rk_source name
        end
    | _ -> failwithf "Cannot classify axiom key %s" key.rk_source
  end axiom_pairs ;
  List.iter begin fun (key, value) ->
    match find_decl_by_id key.rk_prefixed materialized with
    | Some (CTheorem (_, tys, stmt, _)) ->
        let stmt = Thmod_import.map_metaterm_constants substitute stmt in
        if not (Thmod_import.statements_match
                   ~key_params:tys ~key_stmt:stmt
                   ~value_params:value.av_typarams
                   ~value_stmt:value.av_stmt) then
          failwithf
            "Axiom value %s does not have the same statement as key %s"
            value.av_name key.rk_source
    | _ -> failwithf "Cannot classify axiom key %s" key.rk_source
  end axiom_pairs ;
  List.iter begin fun (key, value) ->
    match find_decl_by_id key.rk_prefixed materialized with
    | Some (CDeclPred (_, tps, ty) | CType (_, tps, ty)) ->
        if not (Thmod_import.scheme_matches
                   ~key_params:tps ~key_ty:ty
                   ~value_params:value.pv_typarams
                   ~value_ty:value.pv_ty) then
          failwithf
            "Predicate value %s does not have the same type as key %s"
            value.pv_name key.rk_source
    | _ -> failwithf "Cannot classify predicate key %s" key.rk_source
  end pred_pairs ;
  let axiom_map =
    List.map (fun (key, value) -> (key.rk_prefixed, value.av_tag))
      axiom_pairs
  in
  let final =
    List.filter_map begin fun decl ->
      match decl with
      | CDeclPred (ids, typarams, ty) ->
          let ids =
            List.filter (fun id -> not (List.mem_assoc id pred_map)) ids
          in
          if ids = [] then None else Some (CDeclPred (ids, typarams, ty))
      | CType (ids, typarams, ty) when is_predicate_ty ty ->
          let ids =
            List.filter (fun id -> not (List.mem_assoc id pred_map)) ids
          in
          if ids = [] then None else Some (CType (ids, typarams, ty))
      | CTheorem (id, tys, stmt, fin) ->
          let stmt = Thmod_import.map_metaterm_constants substitute stmt in
          let fin = match List.assoc_opt id axiom_map with
            | Some fin -> fin
            | None -> fin
          in
          Some (CTheorem (id, tys, stmt, fin))
      | CDefine (flavor, typarams, idtys, clauses) ->
          let clauses =
            List.map (fun cl ->
                { head =
                    Thmod_import.map_metaterm_constants substitute cl.head ;
                  body =
                    Thmod_import.map_metaterm_constants substitute cl.body ;
                }) clauses
          in
          Some (CDefine (flavor, typarams, idtys, clauses))
      | CType _ | CKind _ -> Some decl
      | CImport _ | CClose _ | CSuspend _ ->
          failwith "Unexpected declaration in a reasoning module"
    end materialized
  in
  replay_imported_decls final ;
  let instance = {
    Thmod.ins_name = name ;
    ins_source = source ;
    ins_prefix = prefix ;
    ins_decls = final ;
    ins_tyargs = args ;
  } in
  add_import_instance instance ;
  Output.msg_printf "Imported module %s." name



let show_module src =
  let name, params, prefix, content =
    match src with
    | QuoteSource (file, _) ->
        if Filename.check_suffix file ".thmod" then
          failwith "Do not include the .thmod extension in Show Module" ;
        let file = Filepath.normalize ~wrt:!Setup.input file in
        let artifact = load_thmod_artifact ~modname:file in
        let base = Filename.basename file in
        if artifact.ta_name <> base then
          failwithf "Module %s does not match the file name %s.thmod"
            artifact.ta_name base ;
        (artifact.ta_name, artifact.ta_params, [],
         artifact.ta_content)
    | NameSource name ->
        begin match find_import_instance name with
        | Some instance ->
            (instance.Thmod.ins_name, [], instance.Thmod.ins_prefix,
             instance.Thmod.ins_decls)
        | None ->
            begin match Thmod.find_template name with
            | Some template ->
                (template.Thmod.tp_name, template.Thmod.tp_params,
                 template.Thmod.tp_from, template.Thmod.tp_content)
            | None ->
                if List.mem name (Thmod.all_params ()) then
                  failwithf "Module parameter %s is not a module" name ;
                failwithf "Unknown module %s" name
            end
        end
  in
  let summary =
    Thmod.summary_to_string ~name ~params ~prefix content in
  Output.msg_printf "%s" summary

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

let thmod_basename () =
  let base = Filename.basename !Setup.input in
  if Filename.check_suffix base ".thmod" then
    Filename.chop_suffix base ".thmod"
  else base

let check_module_body cmd =
  match cmd with
  | Import _ ->
      failwith "A module may not use ordinary Import"
  | Specification _ ->
      failwith "Specification is not allowed in a module"
  | Close _ ->
      failwith "Close is not allowed in a module"
  | Suspend _ ->
      failwith "Suspend is not allowed in a module"
  | TopCommon Quit ->
      failwith "Quit is not allowed in a module"
  | _ -> ()

let check_thmod_structure cmd =
  match !Setup.file_kind with
  | `thm ->
      if in_module () then check_module_body cmd
  | `thmod -> begin
      match cmd with
      | Module _ ->
          if !Setup.thmod_finished then
            failwith "Module after End is not allowed in a .thmod"
      | End _ ->
          if Thmod.current_name () = None then
            failwith "End without a matching Module"
      | Import _ ->
          failwith "A .thmod may not use ordinary Import"
      | Specification _ ->
          failwith "Specification is not allowed in a .thmod"
      | Close _ ->
          failwith "Close is not allowed in a .thmod"
      | Suspend _ ->
          failwith "Suspend is not allowed in a .thmod"
      | TopCommon Quit ->
          failwith "Quit is not allowed in a .thmod"
      | _ ->
          if !Setup.thmod_finished then
            failwith "Commands after End are not allowed in a .thmod" ;
          if Thmod.current_name () = None then
            failwith "A .thmod must start with a Module command"
    end

let process_module name params =
  match !Setup.file_kind with
  | `thm ->
      if Thmod.current_name () = None &&
         List.exists (fun inst -> inst.Thmod.ins_name = name)
           !thm_instances then
        failwithf "Module name %s is already imported" name ;
      Thmod.push_frame !sr ;
      Thmod.enter_module ~top_path:[name] name params
  | `thmod ->
      let is_top = Thmod.current_name () = None in
      if is_top then begin
        if !Setup.thmod_finished then
          failwith "Module after End is not allowed in a .thmod" ;
        let base = thmod_basename () in
        if name <> base then
          failwithf "Module %s does not match the file name %s.thmod"
            name base ;
        Setup.thmod_name := Some name ;
        Setup.thmod_params := params
      end ;
      Thmod.push_frame !sr ;
      Thmod.enter_module name params

let remove_scope_declarations sc =
  let names =
    List.map (fun item -> item.Thmod.item_name) sc.Thmod.sc_items
  in
  let (ktable, ctable) = !sign in
  sign :=
    (List.filter (fun (id, _) -> not (List.mem id names)) ktable,
     List.filter (fun (id, _) -> not (List.mem id names)) ctable) ;
  Prover.remove_globals names

let process_end name =
  let retain_top = !Setup.file_kind = `thm in
  let closed, is_top = Thmod.leave_module ~retain_top name in
  if not (!Setup.file_kind = `thmod && is_top) then
    remove_scope_declarations closed ;
  sr := Thmod.pop_frame () ;
  if !Setup.file_kind = `thmod && Thmod.current_name () = None then
    Setup.thmod_finished := true

let check_thmod_complete () =
  if !Setup.file_kind = `thmod then
    Thmod.check_complete ()

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
                     | Finished | Axiomatic -> ""
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
      check_thmod_complete () ;
      write_compilation () ;
      if !Setup.mode = `switch then
        perform_switch_to_interactive ()
      else begin
        match !current_state with
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
        | Unify.UnifyError (Unify.InstGenericTyvar (v, ty))
          when List.mem v (bound_params ()) ->
            sprintf
              "Module parameter %s cannot be instantiated to %s."
              v (ty_to_string ty)
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
        show_module src ;
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
  let input =
    if in_module () then
      { input with el = Thmod.resolve_top input.el }
    else
      input
  in
  if !Setup.mode <> `interactive then Output.non_annot "%s.\n%!" cmd_string ;
  check_thmod_structure input.el ;
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
      check_theorem ~bound:(bound_params ()) tys thm ;
      Prover.theorem thm ;
      let oldsign = !sign in
      let thm_compile fin =
        sign := oldsign ;
        compile (CTheorem(name, tys, thm, fin)) ;
        add_lemma ~fin name tys thm
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
  | Axiom(name, tys, thm) ->
      let thm = type_umetaterm ~sr:!sr ~sign:!sign thm in
      check_theorem ~bound:(bound_params ()) tys thm ;
      compile (CTheorem(name, tys, thm, Axiomatic)) ;
      add_lemma ~fin:Axiomatic name tys thm ;
      Setup.axioms := name :: !Setup.axioms
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
        add_lemma ~fin n tys t ;
        compile (CTheorem(n, tys, t, fin))
      end gen_thms ;
      if fin = Unfinished && List.mem name !Setup.unfinished then
        Setup.unfinished :=
          List.map fst gen_thms @ !Setup.unfinished ;
      if fin = Axiomatic && not (List.mem name !Setup.axioms) then
        Setup.axioms :=
          name :: List.map fst gen_thms @ !Setup.axioms ;
  | Define _ ->
      let strat_errors =
        in_module () || stratification_warnings_are_errors
      in
      compile (Prover.register_definition ~strat_errors
                 ~bound_tyvars:(bound_params ()) input.el)
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
  | TopCommon(ShowModule src) -> show_module src
  | TopCommon(Quit) -> raise End_of_file
  | Import(filename, pos, withs) ->
      compile (CImport (filename, withs)) ;
      import ~wrt:!Setup.input pos filename withs
  | Module (name, params) ->
      process_module name params
  | End name ->
      process_end name
  | ImportModule mi ->
      begin match mi.mi_source with
      | QuoteSource (file, pos) ->
          if !Setup.annotate then begin
            let file = Filepath.normalize ~wrt:!Setup.input file in
            Output.link_message ~pos ~url:(file ^ ".html")
          end
      | NameSource _ -> ()
      end ;
      import_module mi
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
  | Close(atys) ->
      Prover.close_types !sign !Prover.clauses atys ;
      compile (CClose(List.map (fun aty -> (aty, Subordination.subordinates !sr aty)) atys))
  end ;
  if not !Setup.annotate then Output.blank_line ()

let () = process1_hook := process1

let initial_snapshot = State.snapshot ()
let () = initial_snapshot_ref := Some initial_snapshot

let welcome_msg = sprintf "Welcome to Abella %s.\n" Version.version
