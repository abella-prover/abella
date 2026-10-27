(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                            en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Pure transformations used when instantiating an imported reasoning
   module. *)

open Term
open Metaterm
open Abella_types
open Typing
open Checks
open Extensions

module Setup = Driver_setup

type renamer = {
  r_const : string -> string ;
  r_tycons : string -> string ;
  r_lemma : string -> string ;
  r_tyvar : string -> string ;
}

let identity = {
  r_const = (fun name -> name) ;
  r_tycons = (fun name -> name) ;
  r_lemma = (fun name -> name) ;
  r_tyvar = (fun name -> name) ;
}

let rec map_ty r (Ty (args, aty)) =
  Ty (List.map (map_ty r) args, map_aty r aty)

and map_aty r = function
  | Tygenvar v -> Tygenvar (r.r_tyvar v)
  | Typtr {contents=TT ty} -> Typtr (ref (TT (map_ty r ty)))
  | Typtr {contents=TV v} -> Typtr (ref (TV (r.r_tyvar v)))
  | Tycons (name, args) ->
      Tycons (r.r_tycons name, List.map (map_ty r) args)

let rec map_term r t =
  match observe (hnorm t) with
  | Var v ->
      let name =
        if v.tag = Constant then r.r_const v.name else v.name
      in
      var v.tag name v.ts (map_ty r v.ty)
  | DB i -> db i
  | Lam (bindings, body) ->
      lambda
        (List.map (fun (id, ty) -> (id, map_ty r ty)) bindings)
        (map_term r body)
  | App (head, args) ->
      app (map_term r head) (List.map (map_term r) args)
  | Ptr _ | Susp _ -> [%bug] "map_term: unexpected pointer or suspension"

let map_obj r obj =
  let context = Context.map (map_term r) obj.context in
  let right = map_term r obj.right in
  let mode = match obj.mode with
    | Async -> Async
    | Sync focus -> Sync (map_term r focus)
  in
  { context ; right ; mode }

let rec map_metaterm r mt =
  match mt with
  | True | False -> mt
  | Eq (a, b) -> Eq (map_term r a, map_term r b)
  | Obj (obj, restriction) -> Obj (map_obj r obj, restriction)
  | Arrow (a, b) -> Arrow (map_metaterm r a, map_metaterm r b)
  | Binding (binder, bindings, body) ->
      let bindings = List.map (fun (id, ty) -> (id, map_ty r ty)) bindings in
      Binding (binder, bindings, map_metaterm r body)
  | Or (a, b) -> Or (map_metaterm r a, map_metaterm r b)
  | And (a, b) -> And (map_metaterm r a, map_metaterm r b)
  | Pred (p, restriction) -> Pred (map_term r p, restriction)

let map_clause r cl =
  { head = map_metaterm r cl.head ;
    body = map_metaterm r cl.body ;
  }

let map_compiled r comp =
  match comp with
  | CTheorem (id, tys, stmt, fin) ->
      CTheorem
        (r.r_lemma id, List.map r.r_tyvar tys, map_metaterm r stmt, fin)
  | CDefine (flavor, typarams, idtys, clauses) ->
      let idtys =
        List.map (fun (id, ty) -> (r.r_const id, map_ty r ty)) idtys
      in
      CDefine
        (flavor, List.map r.r_tyvar typarams, idtys,
         List.map (map_clause r) clauses)
  | CType (ids, typarams, ty) ->
      CType
        (List.map r.r_const ids, List.map r.r_tyvar typarams, map_ty r ty)
  | CDeclPred (ids, typarams, ty) ->
      CDeclPred
        (List.map r.r_const ids, List.map r.r_tyvar typarams, map_ty r ty)
  | CKind (ids, knd) ->
      CKind (List.map r.r_tycons ids, knd)
  | CImport _ | CClose _ | CSuspend _ -> comp

let map_compiled_types f comp =
  let map_clause cl =
    { head = map_on_tys f cl.head ;
      body = map_on_tys f cl.body ;
    }
  in
  match comp with
  | CTheorem (id, tys, stmt, fin) ->
      CTheorem (id, tys, map_on_tys f stmt, fin)
  | CDefine (flavor, typarams, idtys, clauses) ->
      CDefine
        (flavor, typarams,
         List.map (fun (id, ty) -> (id, f ty)) idtys,
         List.map map_clause clauses)
  | CType (ids, typarams, ty) ->
      CType (ids, typarams, f ty)
  | CDeclPred (ids, typarams, ty) ->
      CDeclPred (ids, typarams, f ty)
  | CKind _ | CImport _ | CClose _ | CSuspend _ -> comp

let rec map_term_constants f t =
  match observe (hnorm t) with
  | Var v ->
      let name =
        if v.tag = Constant then f v.name else v.name
      in
      var v.tag name v.ts v.ty
  | DB i -> db i
  | Lam (bindings, body) ->
      lambda bindings (map_term_constants f body)
  | App (head, args) ->
      app (map_term_constants f head)
        (List.map (map_term_constants f) args)
  | Ptr _ | Susp _ ->
      [%bug] "map_term_constants: unexpected pointer or suspension"

let rec map_metaterm_constants f mt =
  match mt with
  | True | False -> mt
  | Eq (a, b) ->
      Eq (map_term_constants f a, map_term_constants f b)
  | Obj (obj, restriction) ->
      let context = Context.map (map_term_constants f) obj.context in
      let right = map_term_constants f obj.right in
      let mode = match obj.mode with
        | Async -> Async
        | Sync focus -> Sync (map_term_constants f focus)
      in
      Obj ({ context ; right ; mode }, restriction)
  | Arrow (a, b) ->
      Arrow (map_metaterm_constants f a, map_metaterm_constants f b)
  | Binding (binder, bindings, body) ->
      Binding (binder, bindings, map_metaterm_constants f body)
  | Or (a, b) ->
      Or (map_metaterm_constants f a, map_metaterm_constants f b)
  | And (a, b) ->
      And (map_metaterm_constants f a, map_metaterm_constants f b)
  | Pred (p, restriction) ->
      Pred (map_term_constants f p, restriction)

let replace_constants f comp =
  match comp with
  | CTheorem (id, tys, stmt, fin) ->
      CTheorem (id, tys, map_metaterm_constants f stmt, fin)
  | CDefine (flavor, typarams, idtys, clauses) ->
      let clauses =
        List.map (fun cl ->
            { head = map_metaterm_constants f cl.head ;
              body = map_metaterm_constants f cl.body ; })
          clauses
      in
      CDefine (flavor, typarams, idtys, clauses)
  | CType _ | CDeclPred _ | CKind _ | CImport _ | CClose _
  | CSuspend _ -> comp

let ids_of_compiled = function
  | CTheorem (id, _, _, _) -> [id]
  | CDefine (_, _, idtys, _) -> List.map fst idtys
  | CType (ids, _, _) | CDeclPred (ids, _, _) | CKind (ids, _) -> ids
  | CImport _ | CClose _ | CSuspend _ -> []

let local_ids decls = List.unique (List.flatten_map ids_of_compiled decls)

let const_ids decls =
  List.unique (List.flatten_map (function
      | CType (ids, _, _) | CDeclPred (ids, _, _) -> ids
      | CDefine (_, _, idtys, _) -> List.map fst idtys
      | CTheorem _ | CKind _ | CImport _ | CClose _ | CSuspend _ -> [])
    decls)

let kind_ids decls =
  List.unique (List.flatten_map (function
      | CKind (ids, _) -> ids
      | _ -> []) decls)

let lemma_ids decls =
  List.unique (List.flatten_map (function
      | CTheorem (id, _, _, _) -> [id]
      | _ -> []) decls)

let typarams_of_compiled = function
  | CTheorem (_, tys, _, _) -> tys
  | CDefine (_, typarams, _, _) -> typarams
  | CType (_, typarams, _) | CDeclPred (_, typarams, _) -> typarams
  | CKind _ | CImport _ | CClose _ | CSuspend _ -> []

let tyvars_of_compiled comp =
  let vars = ref [] in
  ignore begin
    map_compiled_types (fun ty ->
        vars := ty_gentyvars ty @ !vars ; ty)
      comp
  end ;
  List.unique !vars

let join_path path = String.concat "." path

let starts_with prefix s =
  let n = String.length prefix in
  String.length s > n && String.sub s 0 n = prefix

let strip_path prefix name =
  match prefix with
  | [] -> Some name
  | _ ->
      let prefix = join_path prefix in
      if starts_with (prefix ^ ".") name then
        Some (String.sub name (String.length prefix + 1)
                (String.length name - String.length prefix - 1))
      else None

let prefix_name name prefix =
  String.concat "." (prefix @ [name])

let rename_path ~from ~to_ name =
  let from = join_path from in
  let to_ = join_path to_ in
  if from = "" then
    if to_ = "" then name else to_ ^ "." ^ name
  else if name = from then to_
  else if starts_with (from ^ ".") name then
    let rest =
      String.sub name (String.length from)
        (String.length name - String.length from)
    in
    to_ ^ rest
  else
    name

let prefix_renamer ~from ~to_ ~const_ids ~kind_ids ~lemma_ids () =
  let file_rename ids name =
    if List.mem name ids then prefix_name name to_ else name
  in
  {
    r_const = (fun name ->
        if from = [] then file_rename const_ids name
        else rename_path ~from ~to_ name) ;
    r_tycons = (fun name ->
        if from = [] then file_rename kind_ids name
        else rename_path ~from ~to_ name) ;
    r_lemma = (fun name ->
        if from = [] then file_rename lemma_ids name
        else rename_path ~from ~to_ name) ;
    r_tyvar = (fun name -> name) ;
  }

let fresh_tyvar_names count used =
  let used = ref used in
  let rec pick i =
    let name = "A" ^ string_of_int i in
    if List.mem name !used then pick (i + 1)
    else begin
      used := name :: !used ;
      name
    end
  in
  List.init count (fun _ -> pick 1)

let alpha_rename_decl ~avoid comp =
  match typarams_of_compiled comp with
  | [] -> comp
  | typarams ->
      let used = List.unique (avoid @ tyvars_of_compiled comp @ typarams) in
      let fresh = fresh_tyvar_names (List.length typarams) used in
      let pairs = List.combine typarams fresh in
      let rename name =
        match List.assoc_opt name pairs with
        | Some name -> name
        | None -> name
      in
      map_compiled { identity with r_tyvar = rename } comp

let materialize_decl ~renamer ~avoid ~tysub comp =
  comp
  |> map_compiled renamer
  |> alpha_rename_decl ~avoid
  |> map_compiled_types (apply_sub_ty tysub)

let tyvar_subst params args =
  List.map2 (fun param arg -> (param, arg)) params args

let scheme_matches ~key_params ~key_ty ~value_params ~value_ty =
  List.length key_params = List.length value_params &&
  List.exists begin fun perm ->
    let subst =
      List.map2
        (fun param value -> (param, tybase (Tygenvar value)))
        key_params perm
    in
    eq_ty (apply_sub_ty subst key_ty) value_ty
  end (List.permute (List.length value_params) value_params)

let statements_match ~key_params ~key_stmt ~value_params ~value_stmt =
  List.length key_params = List.length value_params &&
  List.exists begin fun perm ->
    let subst =
      List.map2
        (fun param value -> (param, tybase (Tygenvar value)))
        key_params perm
    in
    let key_stmt = map_on_tys (apply_sub_ty subst) key_stmt |> normalize in
    let value_stmt = normalize value_stmt in
    let snap = State.snapshot () in
    try
      meta_right_unify key_stmt value_stmt ;
      State.reload snap ;
      true
    with _ ->
      State.reload snap ;
      false
  end (List.permute (List.length value_params) value_params)

let metaterm_names mt =
  let constants =
    metaterm_support ~tag:Constant mt
    |> List.map (fun t -> (term_to_var t).name)
  in
  let tycons = ref [] in
  let rec collect_ty ty =
    match observe_ty ty with
    | Ty (args, aty) ->
        List.iter collect_ty args ;
        collect_aty aty
  and collect_aty = function
    | Tycons (name, args) ->
        tycons := name :: !tycons ;
        List.iter collect_ty args
    | Typtr {contents=TT ty} -> collect_ty ty
    | Tygenvar _ | Typtr {contents=TV _} -> ()
  in
  ignore (map_on_tys (fun ty -> collect_ty ty ; ty) mt) ;
  List.unique (constants @ !tycons)

let tycons_of_ty ty =
  match observe_ty ty with
  | Ty (args, aty) ->
      let names = ref [] in
      let rec collect_ty ty =
        match observe_ty ty with
        | Ty (args, aty) ->
            List.iter collect_ty args ;
            collect_aty aty
      and collect_aty = function
        | Tycons (name, args) ->
            names := name :: !names ;
            List.iter collect_ty args
        | Typtr {contents=TT ty} -> collect_ty ty
        | Tygenvar _ | Typtr {contents=TV _} -> ()
      in
      List.iter collect_ty args ;
      collect_aty aty ;
      List.unique !names

let summary_to_string ~name ~params ~prefix content =
  let strip name =
    match strip_path prefix name with
    | Some local -> local
    | None -> name
  in
  let renamer = {
    r_const = strip ;
    r_tycons = strip ;
    r_lemma = strip ;
    r_tyvar = (fun id -> id) ;
  } in
  let content = List.map (map_compiled renamer) content in
  let buf = Buffer.create 256 in
  let line fmt =
    Printf.ksprintf
      (fun text -> Buffer.add_string buf text ; Buffer.add_char buf '\n')
      fmt
  in
  let params =
    match params with
    | [] -> ""
    | _ -> "[" ^ String.concat ", " params ^ "]"
  in
  let clause_to_string cl =
    let head = metaterm_to_string cl.head in
    if cl.body = True then head
    else head ^ " := " ^ metaterm_to_string cl.body
  in
  line "Module %s%s." name params ;
  List.iter begin function
    | CKind (ids, knd) ->
        line "  Kind %s %s." (String.concat ", " ids)
          (String.lowercase_ascii (knd_to_string knd))
    | CType (ids, _, ty) | CDeclPred (ids, _, ty) ->
        line "  Type %s %s." (String.concat ", " ids) (ty_to_string ty)
    | CDefine (flavor, _, idtys, clauses) ->
        let keyword =
          match flavor with
          | Inductive -> "Define"
          | CoInductive -> "CoDefine"
        in
        let idtys =
          String.concat ", "
            (List.map (fun (id, ty) -> id ^ " : " ^ ty_to_string ty) idtys)
        in
        line "  %s %s by" keyword idtys ;
        List.iter
          (fun cl -> line "    %s." (clause_to_string cl))
          clauses
    | CTheorem (id, tys, stmt, Axiomatic) ->
        line "  Axiom %s%s : %s." id (gen_to_string tys)
          (metaterm_to_string stmt)
    | CTheorem (id, tys, stmt, _) ->
        line "  Theorem %s%s : %s." id (gen_to_string tys)
          (metaterm_to_string stmt)
    | CImport _ | CClose _ | CSuspend _ ->
        failwith "Unexpected declaration in module summary"
  end content ;
  line "End %s." name ;
  Buffer.contents buf

let in_module () = Thmod.current_name () <> None

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

let resolve_import_target ~(load : modname:string -> Thmod.artifact) mi =
  match mi.mi_source with
  | QuoteSource (file, _) ->
      if Filename.check_suffix file ".thmod" then
        failwith "Do not include the .thmod extension in an import" ;
      let file = Filepath.normalize ~wrt:!Setup.input file in
      let artifact = load ~modname:file in
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
      let instance = Thmod.find_instance name in
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
      match strip_path from id with
      | Some relative -> Some (relative, id, decl)
      | None -> None
    end (ids_of_compiled decl)
  end decls

let find_decl_by_id id decls =
  List.find_some begin fun decl ->
    if List.mem id (ids_of_compiled decl) then Some decl
    else None
  end decls

let materialize_import ~decls ~from ~to_ ~params ~args ~is_instance ~avoid =
  let renamer =
    if is_instance then
      prefix_renamer ~from ~to_
        ~const_ids:[] ~kind_ids:[] ~lemma_ids:[] ()
    else
      prefix_renamer ~from ~to_
        ~const_ids:(const_ids decls)
        ~kind_ids:(kind_ids decls)
        ~lemma_ids:(lemma_ids decls) ()
  in
  let tysub =
    if is_instance then [] else tyvar_subst params args
  in
  let avoid = avoid @ List.flatten_map get_typaram args in
  let materialized =
    List.map (materialize_decl ~renamer ~avoid ~tysub) decls
  in
  let rigid_decls =
    if is_instance then decls
    else List.map (map_compiled renamer) decls
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
          if predicate then renamer.r_const source_id
          else renamer.r_lemma source_id
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
    |> List.map renamer.r_const
  in
  let kinds =
    List.flatten_map (function
        | CKind (ids, _) -> ids
        | _ -> [])
      decls
    |> List.map renamer.r_tycons
  in
  (List.unique consts, List.unique kinds)

let replay_imported_decls ~record decls =
  let replay decl =
    match decl with
    | CImport _ ->
        failwith "Unexpected import in a compiled reasoning module"
    | CClose _ | CSuspend _ ->
        failwith "Unexpected command in a compiled reasoning module"
    | _ ->
        Artifact.install_compiled_decl
          ~strat_errors:true ~subordinate:true decl ;
        record decl
  in
  List.iter replay decls

let import_module
    ~(load : modname:string -> Thmod.artifact) ~record mi =
  let target, default_name, source = resolve_import_target ~load mi in
  let name = match mi.mi_alias with
    | Some alias -> alias
    | None -> default_name
  in
  if List.mem name (Thmod.all_params ()) then
    failwithf "Module name %s is already used as a module parameter" name ;
  begin match mi.mi_alias with
  | None ->
      if Thmod.find_instance name <> None then
        failwithf "Module %s has already been imported" name
  | Some alias ->
      if Thmod.find_instance alias <> None then
        failwithf "Module name %s is already imported" alias ;
      if Thmod.find_template alias <> None then
        failwithf "Module name %s is already in use" alias
  end ;
  let prefix = Thmod.instance_prefix name in
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
      ~params ~args ~is_instance ~avoid:(Thmod.all_params ())
  in
  let rigid =
    List.fold_left begin fun rigid instance ->
      if instance.Thmod.ins_source = source then
        Iset.union rigid
          (Thmod.rigid_predicates_of_decls instance.Thmod.ins_decls)
      else
        rigid
    end rigid (Thmod.all_instances ())
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
            List.intersect (tycons_of_ty ty) target_kinds
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
        let stmt = map_metaterm_constants substitute stmt in
        begin match
            List.intersect
              (metaterm_names stmt)
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
        let stmt = map_metaterm_constants substitute stmt in
        if not (statements_match
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
        if not (scheme_matches
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
          let stmt = map_metaterm_constants substitute stmt in
          let fin = match List.assoc_opt id axiom_map with
            | Some fin -> fin
            | None -> fin
          in
          Some (CTheorem (id, tys, stmt, fin))
      | CDefine (flavor, typarams, idtys, clauses) ->
          let clauses =
            List.map (fun cl ->
                { head = map_metaterm_constants substitute cl.head ;
                  body = map_metaterm_constants substitute cl.body ;
                }) clauses
          in
          Some (CDefine (flavor, typarams, idtys, clauses))
      | CType _ | CKind _ -> Some decl
      | CImport _ | CClose _ | CSuspend _ ->
          failwith "Unexpected declaration in a reasoning module"
    end materialized
  in
  replay_imported_decls ~record final ;
  let instance = {
    Thmod.ins_name = name ;
    ins_source = source ;
    ins_prefix = prefix ;
    ins_decls = final ;
    ins_tyargs = args ;
  } in
  Thmod.add_instance instance ;
  Output.msg_printf "Imported module %s." name

let show_module ~(load : modname:string -> Thmod.artifact) src =
  let name, params, prefix, content =
    match src with
    | QuoteSource (file, _) ->
        if Filename.check_suffix file ".thmod" then
          failwith "Do not include the .thmod extension in Show Module" ;
        let file = Filepath.normalize ~wrt:!Setup.input file in
        let artifact = load ~modname:file in
        let base = Filename.basename file in
        if artifact.ta_name <> base then
          failwithf "Module %s does not match the file name %s.thmod"
            artifact.ta_name base ;
        (artifact.ta_name, artifact.ta_params, [],
         artifact.ta_content)
    | NameSource name ->
        begin match Thmod.find_instance name with
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
    summary_to_string ~name ~params ~prefix content in
  Output.msg_printf "%s" summary
