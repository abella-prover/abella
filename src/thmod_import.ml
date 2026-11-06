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
open Extensions

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
