(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                            en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* .thm-specific state: specifications, the .thc artifact, and ordinary
   source imports. *)

open Term
open Metaterm
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

let add_lemma = Artifact.add_lemma

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

type artifact = {
  thc_spec_sign : Typing.sign ;
  thc_spec_clauses : clause list ;
  thc_predicates : string list ;
  thc_content : compiled list ;
}

let artifact_spec = {
  Artifact.file_kind = `thm ;
  suffix = ".thm" ;
  compiled_suffix = ".thc" ;
  compiling_key = (fun ~modname -> modname) ;
  extract = (fun () -> {
    thc_spec_sign = !Setup.spec_sign ;
    thc_spec_clauses = !Setup.spec_clauses ;
    thc_predicates = Artifact.predicates !sign ;
    thc_content = compiled_content () ;
  }) ;
  encode = (fun art -> [
    Obj.repr art.thc_spec_sign ;
    Obj.repr art.thc_spec_clauses ;
    Obj.repr art.thc_predicates ;
    Obj.repr art.thc_content ;
  ]) ;
  decode = (fun read ->
    let thc_spec_sign = (Obj.obj (read ()) : Typing.sign) in
    let thc_spec_clauses = (Obj.obj (read ()) : clause list) in
    let thc_predicates = (Obj.obj (read ()) : string list) in
    let thc_content = (Obj.obj (read ()) : compiled list) in
    { thc_spec_sign ; thc_spec_clauses ; thc_predicates ; thc_content }) ;
}

let write_compilation () =
  match !Setup.compiled with
  | None -> ()
  | Some compiled -> Artifact.write_compiled artifact_spec compiled

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

let rec process_decls
    ?(import : (string -> (id * id) list -> unit) option)
    ~repl ~modname decls =
  match decls with
  | [] -> ()
  | decl :: decls -> begin
      match decl with
      | CImport(impname, withs) ->
          begin match import with
          | Some import ->
              import (Filepath.normalize ~wrt:modname impname) withs
          | None ->
              failwith "Unexpected import in compiled content"
          end ;
          process_decls ?import ~repl ~modname decls
      | CType(ids, _, (Ty(_, aty) as ty)) when aty = propaty -> begin
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
          process_decls ?import ~repl ~modname
        end
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
          process_decls ?import ~repl ~modname decls
      | CSuspend g ->
          Compute.add_guard g ;
          process_decls ?import ~repl ~modname decls
      | decl ->
          Artifact.install_compiled_decl decl ;
          process_decls ?import ~repl ~modname decls
    end

let rec import ~load ~wrt pos impfile withs =
  let filename = Filepath.normalize ~wrt impfile in
  if List.mem filename !imported then
    Output.msg_printf "Ignoring repeated import: %S." filename
  else begin
    Output.msg_printf "Importing: %S." filename ;
    Output.link_message ~pos ~url:(filename ^ ".html") ;
    import_load ~load filename withs
  end

and import_load ~load modname withs =
  let repl = Replacement.make withs in
  if List.mem modname !imported then () else begin
    imported := modname :: !imported ;
    let art = load ~modname in
    ensure_valid_import
      art.thc_spec_sign art.thc_spec_clauses art.thc_predicates ;
    process_decls ~import:(import_load ~load)
      ~repl ~modname art.thc_content
  end
