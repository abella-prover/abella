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
open Types
open Typing
open Extensions
open Accumulate

module Setup = Driver_setup

let read source =
  Source.read_compiled ~suffix:".thm" ~compiled_suffix:".thc" source

(* Specifications *)

let can_read_specification = State.rref true

let teyjus_only_keywords =
  ["closed"; "exportdef"; "import"; "infix"; "infixl"; "infixr"; "local";
   "localkind"; "postfix"; "posfixl"; "prefix"; "prefixr"; "typeabbrev";
   "use_sig"; "useonly"; "sigma"]

let warn_on_teyjus_only_keywords (ktable, ctable) =
  let tokens =
    List.unique
      (List.map fst (Itab.bindings ktable)
       @ List.map fst (Itab.bindings ctable))
  in
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
      if Itab.mem decl !map then
        failwithf "Duplicate replacement for %s in \"with\"" decl ;
      let pred = UCon (ghost_pos, defn, None) in
      let pred = type_uterm ~sr:!sr ~sign:!sign ~ctx:[] pred in
      map := Itab.add decl { name = defn ; term = pred ; ty = tc [] pred } !map ;
      range := Iset.add defn !range
    end withs ;
    { map = !map ; range = !range }

  let find repl decl = Itab.find decl repl.map
  let mem repl decl = Itab.mem decl repl.map

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
    | CType (ids, _, _) ->
        check_no_existing ids
          ~what:"declared constant"
          ~mem:(fun id -> Itab.mem id repl.map) ;
        comp
    | CSuspend _
    | CClose _ -> comp
end

type artifact = {
  spec_sign : Typing.sign ;
  spec_clauses : clause list ;
  predicates : string list ;
  content : compiled list ;
}

module Spec : Artifact.SPEC with type t = artifact = struct
  type t = artifact

  let file_kind = `thm
  let suffix = ".thm"
  let compiled_suffix = ".thc"
  let compiling_key ~modname = modname

  let extract () = {
    spec_sign = !Setup.spec_sign ;
    spec_clauses = !Setup.spec_clauses ;
    predicates = Artifact.predicates !sign ;
    content = compiled_content () ;
  }

  let encode art = [
    Obj.repr art.spec_sign ;
    Obj.repr art.spec_clauses ;
    Obj.repr art.predicates ;
    Obj.repr art.content ;
  ]

  let decode read =
    let spec_sign = (Obj.obj (read ()) : Typing.sign) in
    let spec_clauses = (Obj.obj (read ()) : clause list) in
    let predicates = (Obj.obj (read ()) : string list) in
    let content = (Obj.obj (read ()) : compiled list) in
    { spec_sign ; spec_clauses ; predicates ; content }
end

module Codec = Artifact.Make (Spec)

let write_compilation () =
  match !Setup.compiled with
  | None -> ()
  | Some compiled -> Codec.write_compiled compiled

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
  let imp_ctable = Itab.filter begin fun _id centry ->
      match centry.pty.ty with
      | Ty (_, aty) when aty = propaty -> false
      | _ -> true
    end imp_ctable in

  (* 1. Imported ktable must be a subset of ktable *)
  let missing_types =
    Itab.fold begin fun id knd acc ->
      match Itab.find_opt id ktable with
      | Some knd' when knd = knd' -> acc
      | _ -> (id, knd) :: acc
    end imp_ktable []
  in
  let () = if missing_types <> [] then
      failwithf "Imported file makes reference to unknown types: %s"
        (String.concat ", " (List.map fst missing_types))
  in

  (* 2. Imported ctable must be a subset of ctable *)
  let missing_consts =
    Itab.fold begin fun id imp_centry acc ->
      match Itab.find_opt id ctable with
      | Some centry when eq_pty imp_centry.pty centry.pty -> acc
      | _ -> (id, imp_centry.pty) :: acc
    end imp_ctable []
  in
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
      | CType(ids, typarams, (Ty(_, aty) as ty)) when aty = propaty -> begin
          let check_types id =
            let open Typing in
            let pred = Replacement.find repl id in
            tid_ensure_fully_inferred ~sign:!sign (pred.name, pred.ty) ;
            if not (eq_ty ty pred.ty) then
              failwithf "Expected type %s:%s, got %s:%s"
                id (ty_to_string ty)
                pred.name (ty_to_string pred.ty)
          in
          let (replaced, unreplaced) =
            List.partition (Replacement.mem repl) ids
          in
          List.iter check_types replaced ;
          begin match unreplaced with
          | [] -> ()
          | _ ->
              CType (unreplaced, typarams, ty)
              |> Replacement.compiled repl
              |> Artifact.install_compiled_decl
          end ;
          List.map (Replacement.compiled repl) decls |>
          process_decls ?import ~repl ~modname
        end
      | CClose(ty_subords) ->
          List.iter
            (fun (ty, prev) ->
               let curr = Subordination.subordinates !sr ty in
               match List.minus ~cmp:eq_aty curr prev with
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
      art.spec_sign art.spec_clauses art.predicates ;
    process_decls ~import:(import_load ~load)
      ~repl ~modname art.content
  end
