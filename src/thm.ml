(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                            en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* .thm-specific state: specifications, the .thc artifact, ordinary
   imports, and inline module scopes. *)

open Term
open Metaterm
open Checks
open Abella_types
open Typing
open Extensions
open Accumulate

module Setup = Driver_setup

let read ?thc source =
  Source.read_compiled ~suffix:".thm" ~compiled_suffix:".thc"
    ?compiled:thc source

(* Specifications *)

let can_read_specification = State.rref true

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

let ensure_finalized_specification () =
  if !can_read_specification then begin
    can_read_specification := false ;
    Setup.spec_sign := !sign ;
    Setup.spec_clauses := !Prover.clauses
  end

(* Compiled content for a .thc artifact *)

let comp_content : compiled list ref = State.rref []

let add_compiled citem =
  comp_content := citem :: !comp_content

let compiled_content () = List.rev !comp_content

let add_lemma ?(fin=Finished) name tys thm =
  match Prover.add_lemma ~fin name tys thm with
  | `replace ->
      Output.msg_printf "Warning: overriding existing lemma named %S." name
  | _ -> ()

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

let thc_layout sign clauses predicates content =
  Artifact.marshal_bytes [
    Obj.repr (Artifact.digest_placeholder ()) ;
    Obj.repr Version.version ;
    Obj.repr sign ;
    Obj.repr clauses ;
    Obj.repr predicates ;
    Obj.repr content ;
  ]

let write_compilation () =
  match !Setup.compiled with
  | None -> ()
  | Some (module Compiled) ->
      Compiled.marshal (Lazy.force Version.self_digest) ;
      Compiled.marshal Version.version ;
      Compiled.marshal !Setup.spec_sign ;
      Compiled.marshal !Setup.spec_clauses ;
      Compiled.marshal (Artifact.predicates !sign) ;
      Compiled.marshal (compiled_content ()) ;
      Compiled.close ()

(* Importing .thm files *)

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
    let module Compiled = (val read thm_path) in
    let recursive_invoke () =
      if not !Setup.recurse then
        failwithf "Recursive invocation of Abella prevented (--non-recursive)" ;
      let cmd = Printf.sprintf " %S -o %S"
          Compiled.path Compiled.out_path in
      [%trace 1 "Running: abella%s" cmd] ;
      if Sys.command (Sys.executable_name ^ cmd) <> 0 then
        failwithf "Could not create %S" Compiled.thc_path
    in
    let use_thc = match !Setup.import_mode with
      | `thc -> true
      | `source -> false
      | `auto -> Source.is_thc_trusted (modname ^ ".thc")
    in
    let bytes =
      if use_thc then begin
        if Compiled.is_stale then recursive_invoke () ;
        read_thc ~modname ~recursive_invoke (Compiled.thc_contents ())
      end
      else source_compile ~modname
    in
    apply_compiled ~repl ~modname bytes
  end

(* Read and validate the four compiled values, recompiling natively if
   the .thc was produced by a different Abella. Returns the bytes to
   marshal from, which may have changed. *)
and read_thc ~modname ~recursive_invoke bytes =
  let unmarshal = Artifact.marshal_reader bytes in
  let dig = (unmarshal () : Digest.t) in
  let ver = (unmarshal () : string) in
  if !Setup.trust_compiled || dig = Lazy.force Version.self_digest then bytes
  else begin
    Output.msg_format
      "@[<v2>Warning: The following .thc file was compiled with a different version (%s) of Abella; recompiling@,%s@]"
      ver (modname ^ ".thc") ;
    recursive_invoke () ;
    let module Compiled = (val read (modname ^ ".thm")) in
    Compiled.thc_contents ()
  end

and apply_compiled ~repl ~modname bytes =
  let read = Artifact.marshal_reader bytes in
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

(* Compile an imported .thm from its source in a pristine sub-session,
   serialize the result in the native .thc layout, then restore the
   parent session. *)
and source_compile ~modname =
  let thm_path = modname ^ ".thm" in
  if List.mem modname !Setup.compiling then
    failwithf "Cyclic import of %S: %s"
      modname
      (String.concat " -> " (List.rev (modname :: !Setup.compiling))) ;
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
  let saved_witnesses = !Setup.witnesses in
  let saved_compiling = !Setup.compiling in
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
    Setup.witnesses := saved_witnesses ;
    Setup.compiling := saved_compiling
  in
  try begin
    State.reload (Option.get !Setup.initial_snapshot) ;
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
    Setup.compiling := modname :: saved_compiling ;
    Output.collect_mode () ;
    ignore (Output.drain ()) ;
    Option.iter (fun f -> f (Source.canon modname)) !Setup.on_import ;
    let rec drive state =
      match !Setup.process1 state with
      | Ok state -> drive state
      | Error _ -> raise (Setup.AbellaExit 1)
    in
    drive Setup.Process_top
  end with
  | Setup.AbellaExit 0 ->
      let spec_sign = !Setup.spec_sign in
      let spec_clauses = !Setup.spec_clauses in
      let predicates = Artifact.predicates !sign in
      let content = compiled_content () in
      let bytes = thc_layout spec_sign spec_clauses predicates content in
      ignore (Output.collected_messages ()) ;
      restore () ;
      Source.add_virtual_thc (modname ^ ".thc") bytes ;
      if Source.virtual_exists (modname ^ ".thc") then
        Source.set_thc_trusted (modname ^ ".thc") true ;
      bytes
  | Setup.AbellaExit n ->
      let text = Output.collected_messages () in
      restore () ;
      failwithf "Could not compile imported module %S (exit %d)%s%s"
        modname n (if text = "" then "" else ": ") text
  | e ->
      let text = Output.collected_messages () in
      restore () ;
      let msg = match e with
        | Failure msg -> msg
        | _ -> sorry e
      in
      failwithf "Could not compile imported module %S: %s%s"
        modname msg (if text = "" then "" else "\n" ^ text)

(* Modules imported into a .thm session *)

let instances : Thmod.instance list ref = State.rref []

let find_instance name =
  List.find_some begin fun inst ->
    if inst.Thmod.ins_name = name then Some inst else None
  end !instances

let add_instance inst =
  if find_instance inst.Thmod.ins_name <> None then
    failwithf "Module name %s is already imported" inst.Thmod.ins_name ;
  instances := !instances @ [inst]

let all_instances () = !instances

(* Inline Module/End in a .thm file *)

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

let check_structure cmd =
  if Thmod.current_name () <> None then check_module_body cmd

let process_module name params =
  if Thmod.current_name () = None &&
     List.exists (fun inst -> inst.Thmod.ins_name = name)
       !instances then
    failwithf "Module name %s is already imported" name ;
  Thmod.push_frame !sr ;
  Thmod.enter_module ~top_path:[name] name params

let process_end name =
  let closed, _ = Thmod.leave_module ~retain_top:true name in
  Thmod.remove_scope_declarations closed ;
  sr := Thmod.pop_frame ()
