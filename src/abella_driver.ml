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
open Setup

let on_import = Setup.on_import
let compiling = Setup.compiling
let witnesses = Setup.witnesses

let thm_instances = Thm.instances
let comp_content = Thm.comp_content
let can_read_specification = Thm.can_read_specification
module Replacement = Thm.Replacement
let process_decls = Thm.process_decls
let collected_messages = Output.collected_messages

let write_compilation () =
  match !Setup.file_kind with
  | `thmod -> Thmod.write_compilation ()
  | `thm -> Thm.write_compilation ()

let is_interactive () = !Setup.mode = `interactive

let in_module () = Thmod.current_name () <> None

let bound_params () =
  if in_module () then Thmod.all_params () else []

exception UserInterrupt = Setup.UserInterrupt
exception AbellaExit = Setup.AbellaExit

type type_error = Setup.type_error = {
  pos : Extensions.pos ;
  actual : Term.ty ;
  expected : Term.ty ;
  kind : Unifyty.constraint_type ;
}

type processing_error = Setup.processing_error =
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

type processing_state = Setup.processing_state =
  | Process_top
  | Process_proof of Setup.proof_processor

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
  else raise @@ AbellaExit 1

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
    comp_content := citem :: !comp_content

let find_import_instance name =
  if in_module () then Thmod.find_instance name
  else Thm.find_instance name

let add_import_instance inst =
  if in_module () then Thmod.add_instance inst
  else Thm.add_instance inst

let import_prefix name =
  if in_module () then Thmod.instance_prefix name else [name]

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

let resolve_import_target mi =
  match mi.mi_source with
  | QuoteSource (file, _) ->
      if Filename.check_suffix file ".thmod" then
        failwith "Do not include the .thmod extension in an import" ;
      let file = Filepath.normalize ~wrt:!Setup.input file in
      let artifact = Thmod.load_artifact ~modname:file in
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
            Thm.add_lemma ~fin name tys stmt
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
        let artifact = Thmod.load_artifact ~modname:file in
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

let check_structure cmd =
  match !Setup.file_kind with
  | `thm -> Thm.check_structure cmd
  | `thmod -> Thmod.check_structure cmd

let process_module name params =
  match !Setup.file_kind with
  | `thm -> Thm.process_module name params
  | `thmod -> Thmod.process_module name params


let process_end name =
  match !Setup.file_kind with
  | `thm -> Thm.process_end name
  | `thmod -> Thmod.process_end name

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
        | UserInterrupt -> User_interrupt
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
          raise @@ AbellaExit 0
      | _ ->
          Output.msg_printf ~severity:Error "Proof NOT Completed." ;
          Output.flush () ;
          raise @@ AbellaExit 1
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
  check_structure input.el ;
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
        Thm.add_lemma ~fin name tys thm
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
      Thm.add_lemma ~fin:Axiomatic name tys thm ;
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
        Thm.add_lemma ~fin n tys t ;
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
        in_module () || stratification_warnings_are_errors
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
  | TopCommon(ShowModule src) -> show_module src ; Process_top
  | TopCommon(Quit) -> raise End_of_file
  | Import(filename, pos, withs) ->
      compile (CImport (filename, withs)) ;
      Thm.import ~wrt:!Setup.input pos filename withs ;
      Process_top
  | Module (name, params) ->
      process_module name params ;
      Process_top
  | End name ->
      process_end name ;
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
      import_module mi ;
      Process_top
  | Specification(filename, pos) ->
      (if !can_read_specification then begin
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

let () = Setup.process1 := process1

let initial_snapshot = State.snapshot ()
let () = Setup.initial_snapshot := Some initial_snapshot

let welcome_msg = sprintf "Welcome to Abella %s.\n" Version.version
