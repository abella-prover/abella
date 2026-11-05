(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                            en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Module environments, name resolution, and artifact-relative naming for
   reasoning-level modules. Internal names are stored relative to the
   top-level module: a direct item is [x], and an item in the nested
   module [Bar] is [Bar.x]. *)

open Term
open Typing
open Metaterm
open Abella_types
open Extensions

module Setup = Driver_setup

let read ?thmodc source =
  Source.read_compiled ~suffix:".thmod" ~compiled_suffix:".thmodc"
    ?compiled:thmodc source

type item_class =
  | KindItem
  | TypeItem
  | PredicateItem
  | DefineItem
  | TheoremItem
  | AxiomItem

type item = {
  item_local : string ;
  item_name : string ;
  item_class : item_class ;
  item_ty : ty option ;
  item_typarams : string list ;
}

type template = {
  tp_name : string ;
  tp_from : string list ;
  tp_source : string ;
  tp_params : string list ;
  tp_content : compiled list ;
  tp_nested : string list ;
}

type instance = {
  ins_name : string ;
  ins_source : string ;
  ins_prefix : string list ;
  ins_decls : compiled list ;
  ins_tyargs : ty list ;
}

type scope = {
  sc_name : string ;
  sc_root : string ;
  sc_source : string ;
  sc_path : string list ;
  sc_params : string list ;
  sc_items : item list ;
  sc_children : scope list ;
  sc_instances : (string * instance) list ;
  sc_content : compiled list ;      (* reverse declaration order *)
}

type env = {
  en_stack : scope list ;           (* innermost first *)
  en_top : scope option ;
  en_templates : scope list ;       (* completed top-level .thm modules *)
  en_complete : bool ;
}

let initial_env = {
  en_stack = [] ;
  en_top = None ;
  en_templates = [] ;
  en_complete = false ;
}

let env = State.rref initial_env
let frames : Subordination.sr list ref = State.rref []

let identity_display name = name

let reset () =
  env := initial_env ;
  frames := [] ;
  Term.display_name := identity_display

let starts_with prefix s =
  let n = String.length prefix in
  String.length s > n && String.sub s 0 n = prefix

let strip_prefix prefix name =
  String.sub name (String.length prefix + 1)
    (String.length name - String.length prefix - 1)

let rec display_name_for prefixes name =
  match prefixes with
  | [] -> name
  | path :: rest ->
      let prefix = String.concat "." path in
      if prefix = "" then name
      else if starts_with (prefix ^ ".") name then
        strip_prefix prefix name
      else
        display_name_for rest name

let update_display () =
  match !env.en_stack with
  | [] -> Term.display_name := identity_display
  | sc :: rest ->
      let prefixes =
        List.map (fun sc -> sc.sc_path) (sc :: rest)
      in
      Term.display_name := fun name -> display_name_for prefixes name

let current_scope () =
  match !env.en_stack with
  | sc :: _ -> Some sc
  | [] -> None

let current_name () =
  match current_scope () with
  | Some sc -> Some sc.sc_name
  | None -> None

let instance_prefix name =
  match current_scope () with
  | Some sc -> sc.sc_path @ [name]
  | None -> [name]

let template_of_scope sc = {
  tp_name = sc.sc_name ;
  tp_from = sc.sc_path ;
  tp_source = sc.sc_source ;
  tp_params = sc.sc_params ;
  tp_content = List.rev sc.sc_content ;
  tp_nested = List.map (fun ch -> ch.sc_name) sc.sc_children ;
}

let find_template name =
  let in_current =
    match current_scope () with
    | None -> None
    | Some sc ->
        List.find_some begin fun ch ->
          if ch.sc_name = name then Some (template_of_scope ch) else None
        end sc.sc_children
  in
  match in_current with
  | Some _ as template -> template
  | None ->
      List.find_some begin fun sc ->
        if sc.sc_name = name then Some (template_of_scope sc) else None
      end !env.en_templates

let find_instance name =
  match current_scope () with
  | None -> None
  | Some sc -> List.assoc_opt name sc.sc_instances

let add_instance inst =
  match !env.en_stack with
  | [] -> failwith "Cannot import a module outside a module"
  | sc :: rest ->
      if List.mem_assoc inst.ins_name sc.sc_instances then
        failwithf "Module name %s is already imported" inst.ins_name ;
      let sc = { sc with
                 sc_instances = sc.sc_instances @ [(inst.ins_name, inst)] } in
      env := { !env with en_stack = sc :: rest }

let top_scope () = !env.en_top

let top_name () =
  match top_scope () with
  | Some sc -> Some sc.sc_name
  | None -> None

let top_params () =
  match top_scope () with
  | Some sc -> sc.sc_params
  | None -> []

let enclosing_scopes () =
  match !env.en_stack with
  | [] -> []
  | _ :: rest -> rest

let all_params () =
  List.flatten_map (fun sc -> sc.sc_params) (List.rev !env.en_stack)

let all_items () =
  List.flatten_map (fun sc -> sc.sc_items) !env.en_stack

let all_instances () =
  List.flatten_map (fun sc -> List.map snd sc.sc_instances) !env.en_stack

let lookup_item_in items name =
  List.find_some begin fun it ->
    if it.item_local = name then Some it else None
  end items

let lookup_item name =
  lookup_item_in (all_items ()) name

let lookup_item_by_name name =
  List.find_some begin fun it ->
    if it.item_name = name then Some it else None
  end (all_items ())

let enclosing_items () =
  List.flatten_map (fun sc -> sc.sc_items) (enclosing_scopes ())

let all_module_names () =
  let rec descend sc =
    List.flatten_map descend sc.sc_children
  in
  let scopes = !env.en_stack in
  let names =
    List.flatten_map (fun sc ->
        let children =
          List.flatten_map (fun ch -> ch.sc_name :: descend ch) sc.sc_children
        in
        children @ List.map fst sc.sc_instances)
      scopes
  in
  let templates = List.map (fun sc -> sc.sc_name) !env.en_templates in
  let stack_top =
    match List.rev scopes with
    | sc :: _ -> [sc.sc_name]
    | [] -> []
  in
  let names =
    match !env.en_top with
    | Some sc -> sc.sc_name :: names
    | None -> stack_top @ names
  in
  List.unique (templates @ names)

let all_child_names () =
  match current_scope () with
  | None -> []
  | Some sc ->
      List.map (fun ch -> ch.sc_name) sc.sc_children @
      List.map fst sc.sc_instances

let split_qualified name =
  String.split_on_char '.' name

let last_segment name =
  match List.rev (split_qualified name) with
  | last :: _ -> last
  | [] -> name

let validate_final_segment name =
  let last = last_segment name in
  if List.mem last (all_module_names ()) then
    failwithf "Module name %s is not an item" last ;
  if List.mem last (all_params ()) then
    failwithf "Module parameter %s is not an item" last

let is_dotted name = String.contains name '.'

let validate_qualified name =
  validate_final_segment name ;
  match split_qualified name with
  | [] | [_] -> ()
  | prefix :: _ ->
      if List.mem prefix (all_params ()) then
        failwithf "Module parameter %s is not a module" prefix ;
      if lookup_item_in (all_items ()) name <> None then ()
      else if List.mem prefix (all_child_names ()) then
        let is_instance =
          match current_scope () with
          | Some sc -> List.mem_assoc prefix sc.sc_instances
          | None -> false
        in
        if is_instance then
          failwithf "Unknown item %s in module %s" name prefix
        else
          failwithf
            "Module %s has not been imported; item %s is not in scope"
            prefix name
      else
        failwithf "Unknown module %s in qualified name %s" prefix name

let resolve_dotted name =
  validate_qualified name ;
  match lookup_item_in (all_items ()) name with
  | Some it -> it.item_name
  | None -> name

let resolve_id name =
  if is_dotted name then resolve_dotted name
  else begin
    match lookup_item name with
    | Some it -> it.item_name
    | None -> name
  end

let resolve_type_name name =
  if is_dotted name then resolve_dotted name
  else begin
    match lookup_item name with
    | Some it -> it.item_name
    | None -> name
  end

let new_name name =
  match !env.en_stack with
  | [] -> name
  | sc :: _ -> String.concat "." (sc.sc_path @ [name])

let resolve_locals locals name =
  match List.assoc_opt name locals with
  | Some name -> name
  | None -> resolve_id name

let rec resolve_aty aty =
  match aty with
  | Tygenvar _ -> aty
  | Typtr {contents=TT ty} -> Typtr (ref (TT (resolve_ty ty)))
  | Typtr {contents=TV v} -> Typtr (ref (TV v))
  | Tycons (name, args) ->
      Tycons (resolve_type_name name, List.map resolve_ty args)

and resolve_ty (Ty (args, aty)) =
  Ty (List.map resolve_ty args, resolve_aty aty)

let rec resolve_uterm ?(locals=[]) t =
  match t with
  | UCon (pos, name, ty) ->
      UCon (pos, resolve_locals locals name, resolve_ty ty)
  | ULam (pos, name, ty, body) ->
      ULam (pos, name, resolve_ty ty, resolve_uterm ~locals body)
  | UApp (pos, t1, t2) ->
      UApp (pos, resolve_uterm ~locals t1, resolve_uterm ~locals t2)

let rec resolve_umetaterm ?(locals=[]) mt =
  match mt with
  | UTrue | UFalse -> mt
  | UEq (t1, t2) ->
      UEq (resolve_uterm ~locals t1, resolve_uterm ~locals t2)
  | UAsyncObj (l, g, r) ->
      UAsyncObj
        (resolve_uterm ~locals l, resolve_uterm ~locals g, r)
  | USyncObj (l, f, g, r) ->
      USyncObj
        (resolve_uterm ~locals l, resolve_uterm ~locals f,
         resolve_uterm ~locals g, r)
  | UArrow (a, b) ->
      UArrow (resolve_umetaterm ~locals a, resolve_umetaterm ~locals b)
  | UBinding (binder, tids, body) ->
      let tids =
        List.map (fun (id, ty) -> (id, resolve_ty ty)) tids
      in
      UBinding (binder, tids, resolve_umetaterm ~locals body)
  | UOr (a, b) ->
      UOr (resolve_umetaterm ~locals a, resolve_umetaterm ~locals b)
  | UAnd (a, b) ->
      UAnd (resolve_umetaterm ~locals a, resolve_umetaterm ~locals b)
  | UPred (p, r) -> UPred (resolve_uterm ~locals p, r)

let check_no_module_param_listing tys =
  match List.intersect tys (all_params ()) with
  | [] -> ()
  | param :: _ ->
      failwithf
        "Module parameter %s may not be listed as a declaration-local type \
         parameter" param

let resolve_top cmd =
  match cmd with
  | Theorem (name, tys, body) ->
      check_no_module_param_listing tys ;
      Theorem (new_name name, tys, resolve_umetaterm body)
  | Axiom (name, tys, body) ->
      check_no_module_param_listing tys ;
      Axiom (new_name name, tys, resolve_umetaterm body)
  | Define (flavor, idtys, clauses) ->
      let locals =
        List.map (fun (id, _) -> (id, new_name id)) idtys
      in
      let idtys =
        List.map (fun (id, ty) -> (List.assoc id locals, resolve_ty ty))
          idtys
      in
      let clauses =
        List.map (fun (head, body) ->
            (resolve_umetaterm ~locals head, resolve_umetaterm ~locals body))
          clauses
      in
      Define (flavor, idtys, clauses)
  | Kind (ids, knd) ->
      Kind (List.map new_name ids, knd)
  | Type (ids, ty) ->
      Type (List.map new_name ids, resolve_ty ty)
  | SSplit (name, names) ->
      SSplit (resolve_id name, names)
  | Query mt ->
      Query (resolve_umetaterm mt)
  | TopCommon (Show name) ->
      TopCommon (Show (resolve_id name))
  | Import _ | ImportModule _ | Module _ | End _ | Specification _
  | Close _ | Suspend _ | TopCommon _ -> cmd

let resolve_hyp_or_item ~is_hyp name =
  if not (is_dotted name) && is_hyp name then name
  else resolve_id name

let resolve_clearable ~is_hyp = function
  | Keep (name, tys) -> Keep (resolve_hyp_or_item ~is_hyp name, tys)
  | Remove (name, tys) -> Remove (resolve_hyp_or_item ~is_hyp name, tys)

let rec resolve_witness ~is_hyp w =
  match w with
  | WTrue | WReflexive | WMagic -> w
  | WHyp _ -> w
  | WLeft w -> WLeft (resolve_witness ~is_hyp w)
  | WRight w -> WRight (resolve_witness ~is_hyp w)
  | WSplit (a, b) ->
      WSplit (resolve_witness ~is_hyp a, resolve_witness ~is_hyp b)
  | WForall (ids, w) -> WForall (ids, resolve_witness ~is_hyp w)
  | WIntros (ids, w) -> WIntros (ids, resolve_witness ~is_hyp w)
  | WExists (bs, w) ->
      WExists (bs, resolve_witness ~is_hyp w)
  | WUnfold (name, n, ws) ->
      WUnfold (resolve_id name, n,
               List.map (resolve_witness ~is_hyp) ws)

let resolve_ewitness ew =
  match ew with
  | ETerm t -> ETerm (resolve_uterm t)
  | ESub (x, t) -> ESub (x, resolve_uterm t)

let resolve_clause_selector = function
  | Select_named name -> Select_named (resolve_id name)
  | (Select_any | Select_num _) as sel -> sel

let resolve_command ~is_hyp cmd =
  match cmd with
  | Induction _ | CoInduction _ | Clear _ | ClearDups | Abbrev _
  | Unabbrev _ | Rename _ | Permute _ | Intros _ | Skip -> cmd
  | Apply (depth, h, args, ws, hint) ->
      let h = resolve_clearable ~is_hyp h in
      let args = List.map (resolve_clearable ~is_hyp) args in
      let ws =
        List.map (fun (x, t) -> (x, resolve_uterm t)) ws
      in
      Apply (depth, h, args, ws, hint)
  | Backchain (depth, h, ws) ->
      let h = resolve_clearable ~is_hyp h in
      let ws = List.map (fun (x, t) -> (x, resolve_uterm t)) ws in
      Backchain (depth, h, ws)
  | Compute (hs, gas, hint) ->
      Compute (List.map (resolve_clearable ~is_hyp) hs, gas, hint)
  | CutFrom (h, arg, t, hint) ->
      CutFrom (resolve_clearable ~is_hyp h,
               resolve_clearable ~is_hyp arg,
               resolve_uterm t, hint)
  | Cut (h, arg, hint) ->
      Cut (resolve_clearable ~is_hyp h,
           resolve_clearable ~is_hyp arg, hint)
  | SearchCut (h, hint) ->
      SearchCut (resolve_clearable ~is_hyp h, hint)
  | Inst (h, ws, hint) ->
      let ws = List.map (fun (x, t) -> (x, resolve_uterm t)) ws in
      Inst (resolve_clearable ~is_hyp h, ws, hint)
  | Case (h, hint) -> Case (resolve_clearable ~is_hyp h, hint)
  | Assert (t, depth, hint) ->
      Assert (resolve_umetaterm t, depth, hint)
  | Monotone (h, t, hint) ->
      Monotone (resolve_clearable ~is_hyp h, resolve_uterm t, hint)
  | Exists (kind, ews) ->
      Exists (kind, List.map resolve_ewitness ews)
  | Search bounds ->
      let bounds = match bounds with
        | `witness w -> `witness (resolve_witness ~is_hyp w)
        | _ -> bounds
      in
      Search bounds
  | Unfold (cs, ss) ->
      Unfold (resolve_clause_selector cs, ss)
  | Saturate sat ->
      let lemmas = List.map (resolve_hyp_or_item ~is_hyp) sat.lemmas in
      Saturate ({ sat with lemmas })
  | Common (Show name) ->
      Common (Show (resolve_hyp_or_item ~is_hyp name))
  | Common Quit ->
      failwith "Quit is not allowed in a module"
  | ComputeAll _ | Split | SplitStar | Left | Right | Undo
  | Common _ -> cmd
  | Abort ->
      failwith "Abort is not allowed in a module"

let resolve_proof_command = resolve_command

(* Classification and declaration registration *)

let is_predicate_ty ty =
  match observe_ty ty with
  | Ty (_, aty) -> aty = propaty

let class_of_compiled = function
  | CKind _ -> Some KindItem
  | CDeclPred _ -> Some PredicateItem
  | CType (_, _, ty) ->
      Some (if is_predicate_ty ty then PredicateItem else TypeItem)
  | CDefine _ -> Some DefineItem
  | CTheorem (_, _, _, Axiomatic) -> Some AxiomItem
  | CTheorem _ -> Some TheoremItem
  | CImport _ | CClose _ | CSuspend _ -> None

let items_of_compiled ?(local=last_segment) citem =
  match citem with
  | CKind (ids, _) ->
      List.map (fun id ->
          { item_local = local id ;
            item_name = id ;
            item_class = KindItem ;
            item_ty = None ;
            item_typarams = [] }) ids
  | CDeclPred (ids, typarams, ty) ->
      List.map (fun id ->
          { item_local = local id ;
            item_name = id ;
            item_class = PredicateItem ;
            item_ty = Some ty ;
            item_typarams = typarams }) ids
  | CType (ids, typarams, ty) ->
      let cls = if is_predicate_ty ty then PredicateItem else TypeItem in
      List.map (fun id ->
          { item_local = local id ;
            item_name = id ;
            item_class = cls ;
            item_ty = Some ty ;
            item_typarams = typarams }) ids
  | CDefine (_, typarams, idtys, _) ->
      List.map (fun (id, ty) ->
          { item_local = local id ;
            item_name = id ;
            item_class = DefineItem ;
            item_ty = Some ty ;
            item_typarams = typarams }) idtys
  | CTheorem (id, typarams, _, fin) ->
      [{ item_local = local id ;
         item_name = id ;
         item_class =
           (if fin = Axiomatic then AxiomItem else TheoremItem) ;
         item_ty = None ;
         item_typarams = typarams }]
  | CImport _ | CClose _ | CSuspend _ -> []

let check_shadowing sc new_items =
  let enclosing = enclosing_items () in
  List.iter begin fun item ->
    if lookup_item_in enclosing item.item_local <> None then
      failwithf
        "Declaration %s shadows a declaration in an enclosing module"
        item.item_local ;
    if lookup_item_in sc.sc_items item.item_local <> None then
      failwithf "Declaration %s already exists in this module"
        item.item_local
  end new_items

let relative_to_current_scope id =
  match current_scope () with
  | None -> id
  | Some sc ->
      match sc.sc_path with
      | [] -> id
      | _ ->
          let prefix = String.concat "." sc.sc_path in
          if starts_with (prefix ^ ".") id then strip_prefix prefix id
          else id

let add_compiled ?(imported=false) citem =
  match !env.en_stack with
  | [] -> failwith "Cannot add a declaration outside a module"
  | sc :: rest ->
      let local =
        if imported then relative_to_current_scope else last_segment
      in
      let new_items = items_of_compiled ~local citem in
      check_shadowing sc new_items ;
      let sc = { sc with
                 sc_items = sc.sc_items @ new_items ;
                 sc_content = citem :: sc.sc_content } in
      env := { !env with en_stack = sc :: rest } ;
      update_display ()

let add_imported_compiled citem = add_compiled ~imported:true citem

let check_param_shadowing params =
  if List.length params <> List.length (List.unique params) then
    failwith "Duplicate module parameter" ;
  List.iter begin fun param ->
    if List.mem param (all_params ()) then
      failwithf "Module parameter %s shadows an enclosing parameter" param
  end params

let enter_module ?(top_path=[]) name params =
  let state = !env in
  if state.en_complete then
    failwith "Module after End is not allowed in a .thmod" ;
  check_param_shadowing params ;
  match state.en_stack with
  | [] ->
      if List.exists (fun sc -> sc.sc_name = name) state.en_templates then
        failwithf "Module %s is already declared" name ;
      let sc = { sc_name = name ;
                 sc_root = name ;
                 sc_source = "inline:" ^ name ;
                 sc_path = top_path ;
                 sc_params = params ;
                 sc_items = [] ;
                 sc_children = [] ;
                 sc_instances = [] ;
                 sc_content = [] } in
      env := { state with en_stack = [sc] } ;
      update_display ()
  | parent :: _ ->
      if List.exists (fun ch -> ch.sc_name = name) parent.sc_children then
        failwithf "Module %s is already declared in this module" name ;
      if List.mem_assoc name parent.sc_instances then
        failwithf "Module %s is already imported in this module" name ;
      let sc = { sc_name = name ;
                 sc_root = parent.sc_root ;
                 sc_source = parent.sc_source ^ "." ^ name ;
                 sc_path = parent.sc_path @ [name] ;
                 sc_params = params ;
                 sc_items = [] ;
                 sc_children = [] ;
                 sc_instances = [] ;
                 sc_content = [] } in
      env := { state with en_stack = sc :: state.en_stack } ;
      update_display ()

let leave_module ?(retain_top=false) name =
  match !env.en_stack with
  | [] -> failwith "End without a matching Module"
  | sc :: rest ->
      if sc.sc_name <> name then
        failwithf "End %s does not match Module %s" name sc.sc_name ;
      begin match rest with
      | [] when retain_top ->
          env := { !env with
                   en_stack = [] ;
                   en_templates = sc :: !env.en_templates }
      | [] ->
          env := { !env with
                   en_stack = [] ; en_top = Some sc ; en_complete = true }
      | parent :: parents ->
          let parent =
            { parent with sc_children = parent.sc_children @ [sc] }
          in
          env := { !env with en_stack = parent :: parents }
      end ;
      update_display () ;
      (sc, rest = [])

let check_complete () =
  let state = !env in
  if state.en_top = None then
    failwith "A .thmod must contain a top-level module" ;
  match state.en_stack with
  | sc :: _ -> failwithf "Missing End for module %s" sc.sc_name
  | [] -> ()

let push_frame sr = frames := sr :: !frames

let pop_frame () =
  match !frames with
  | sr :: rest -> frames := rest ; sr
  | [] -> failwith "No saved subordination frame"

let summary_to_string ~name ~params ~prefix content =
  let strip name =
    match Thmod_import.strip_path prefix name with
    | Some local -> local
    | None -> name
  in
  let renamer = {
    Thmod_import.r_const = strip ;
    r_tycons = strip ;
    r_lemma = strip ;
    r_tyvar = (fun id -> id) ;
  } in
  let content = List.map (Thmod_import.map_compiled renamer) content in
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

let exported_content () =
  match top_scope () with
  | Some sc -> List.rev sc.sc_content
  | None -> []

let exported_names () =
  match top_scope () with
  | Some sc -> List.map (fun it -> it.item_name) sc.sc_items
  | None -> []

let nested_module_names () =
  match top_scope () with
  | Some sc -> List.map (fun ch -> ch.sc_name) sc.sc_children
  | None -> []

let is_key = function
  | PredicateItem | AxiomItem -> true
  | KindItem | TypeItem | DefineItem | TheoremItem -> false

let keys_of_items items =
  List.filter (fun it -> is_key it.item_class) items

let keys_of_decls decls =
  List.flatten_map items_of_compiled decls |> keys_of_items

let predicate_result_ty ty =
  match observe_ty ty with
  | Ty (_, aty) -> aty = propaty

let local_scheme decls name =
  let rec aux = function
    | [] -> None
    | CDeclPred (ids, _, ty) :: rest
    | CType (ids, _, ty) :: rest ->
        if List.mem name ids then Some ty else aux rest
    | CDefine (_, _, idtys, _) :: rest ->
        begin match List.assoc_opt name idtys with
        | Some ty -> Some ty
        | None -> aux rest
        end
    | _ :: rest -> aux rest
  in
  aux decls

let sign_scheme name = List.assoc_opt name (snd !sign)

let pervasive_constants =
  List.map fst (snd pervasive_sign)

let is_predicate_name decls name =
  if List.mem name pervasive_constants then false
  else
    match local_scheme decls name with
    | Some ty -> predicate_result_ty ty
    | None ->
        match sign_scheme name with
        | Some (Poly (_, ty)) -> predicate_result_ty ty
        | None -> false

let constants_of_metaterm mt =
  metaterm_support ~tag:Constant mt
  |> List.map (fun t -> (term_to_var t).name)

let constants_of_compiled = function
  | CTheorem (_, _, mt, _) -> constants_of_metaterm mt
  | CDefine (_, _, _, clauses) ->
      List.flatten_map (fun cl ->
          constants_of_metaterm cl.head @ constants_of_metaterm cl.body)
        clauses
  | CDeclPred (_, _, ty)
  | CType (_, _, ty) ->
      (* Predicate constants can only occur in types through higher-order
         constants, which declared predicates cannot have. *)
      let _ = ty in
      []
  | CKind _ | CImport _ | CClose _ | CSuspend _ -> []

let declared_predicates_of_compiled = function
  | CDeclPred (ids, _, _) -> ids
  | CType (ids, _, ty) when is_predicate_ty ty -> ids
  | CDefine (_, _, idtys, _) -> List.map fst idtys
  | _ -> []

let rigid_predicates_of_decls decls =
  let declared =
    List.flatten_map declared_predicates_of_compiled decls
  in
  let occurring = List.flatten_map constants_of_compiled decls in
  let candidates = List.unique (declared @ occurring) in
  let predicates = List.find_all (is_predicate_name decls) candidates in
  Iset.of_list predicates

(* .thmod artifacts, file structure, and source compilation *)

type artifact = {
  ta_name : string ;
  ta_params : string list ;
  ta_content : compiled list ;
  ta_nested : string list ;
  ta_exports : string list ;
}

let parse_artifact bytes =
  let read = Artifact.marshal_reader bytes in
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

let loading : string list ref = State.rref []

let recompile ~path ~out_path =
  if not !Setup.recurse then
    failwithf "Recursive invocation of Abella prevented (--non-recursive)" ;
  let cmd = Printf.sprintf " %S -o %S" path out_path in
  [%trace 1 "Running: abella%s" cmd] ;
  if Sys.command (Sys.executable_name ^ cmd) <> 0 then
    failwithf "Could not create the compiled form of %S" path

let rec load_artifact ~modname =
  let path = modname ^ ".thmod" in
  let canonical = Source.canon path in
  if List.mem canonical !loading then
    failwithf "Cyclic import of %S: %s"
      path (String.concat " -> " (List.rev (canonical :: !loading))) ;
  let saved_loading = !loading in
  loading := canonical :: saved_loading ;
  Fun.protect ~finally:(fun () -> loading := saved_loading)
    begin fun () ->
      let module Src = (val read path) in
      let recursive_invoke () =
        recompile ~path:Src.path ~out_path:Src.out_path
      in
      let use_artifact = match !Setup.import_mode with
        | `thc -> true
        | `source -> false
        | `auto -> Source.is_thc_trusted Src.thc_path
      in
      if Source.virtual_exists path then begin
        if not use_artifact || Src.is_stale then
          ignore (source_compile ~modname)
      end else if not use_artifact || Src.is_stale then
        recursive_invoke () ;
      let bytes = Src.thc_contents () in
      let read_digest bytes =
        let read = Artifact.marshal_reader bytes in
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
        parse_artifact (Src.thc_contents ())
      end else
        parse_artifact bytes
    end

and source_compile ~modname =
  let thmod_path = modname ^ ".thmod" in
  let compiling_key = modname ^ ".thmod" in
  if List.mem compiling_key !Setup.compiling then
    failwithf "Cyclic import of %S: %s"
      thmod_path
      (String.concat " -> " (List.rev (compiling_key :: !Setup.compiling))) ;
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
  let saved_witnesses = !Setup.witnesses in
  let saved_state = !Setup.current_state in
  let saved_compiling = !Setup.compiling in
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
    Setup.witnesses := saved_witnesses ;
    Setup.current_state := saved_state ;
    Setup.compiling := saved_compiling ;
    Typing.clause_map := saved_clause_map
  in
  try begin
    State.reload (Option.get !Setup.initial_snapshot) ;
    reset () ;
    State.Undo.set_enabled false ;
    Setup.mode := `batch ;
    Setup.annotate := false ;
    Setup.recurse := false ;
    Setup.compiled := None ;
    Setup.unfinished := [] ;
    Setup.input := thmod_path ;
    Setup.file_kind := `thmod ;
    let module Src = (val read thmod_path) in
    Setup.lexbuf := Src.lex true ;
    Setup.compiling := compiling_key :: saved_compiling ;
    Output.collect_mode () ;
    ignore (Output.drain ()) ;
    Option.iter (fun f -> f (Source.canon thmod_path)) !Setup.on_import ;
    let rec drive () =
      match !Setup.process1 () with
      | `ok -> drive ()
      | `error -> raise (Setup.AbellaExit 1)
    in
    drive ()
  end with
  | Setup.AbellaExit 0 ->
      let name = match top_name () with
        | Some name -> name
        | None -> failwith "A .thmod must contain a top-level module"
      in
      let params = top_params () in
      let content = exported_content () in
      let nested = nested_module_names () in
      let exports = exported_names () in
      let artifact_sign = sign_of_content content in
      let preds =
        Artifact.predicates artifact_sign |>
        List.filter (fun id -> List.mem id exports)
      in
      let bytes =
        thmodc_layout name params artifact_sign !Setup.spec_clauses preds
          content nested exports
      in
      ignore (Output.collected_messages ()) ;
      restore () ;
      Source.add_virtual_thc (modname ^ ".thmodc") bytes ;
      if Source.virtual_exists (modname ^ ".thmodc") then
        Source.set_thc_trusted (modname ^ ".thmodc") true ;
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

and sign_of_content content =
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

and thmodc_layout name params sign clauses predicates content nested exports =
  Artifact.marshal_bytes [
    Obj.repr (Artifact.digest_placeholder ()) ;
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

and write_compilation () =
  match !Setup.compiled with
  | None -> ()
  | Some (module Compiled) ->
      let name = match top_name () with
        | Some name -> name
        | None -> failwith "Cannot write a .thmodc without a module"
      in
      let content = exported_content () in
      let exports = exported_names () in
      let preds =
        Artifact.predicates !sign |>
        List.filter (fun id -> List.mem id exports)
      in
      Compiled.marshal (Lazy.force Version.self_digest) ;
      Compiled.marshal Version.version ;
      Compiled.marshal name ;
      Compiled.marshal (top_params ()) ;
      Compiled.marshal (sign_of_content content) ;
      Compiled.marshal !Setup.spec_clauses ;
      Compiled.marshal preds ;
      Compiled.marshal content ;
      Compiled.marshal (nested_module_names ()) ;
      Compiled.marshal exports ;
      Compiled.close ()

(* File structure *)

let is_complete () = (!env).en_complete

let basename () =
  let base = Filename.basename !Setup.input in
  if Filename.check_suffix base ".thmod" then
    Filename.chop_suffix base ".thmod"
  else base

let check_structure cmd =
  match cmd with
  | Module _ ->
      if is_complete () then
        failwith "Module after End is not allowed in a .thmod"
  | End _ ->
      if current_name () = None then
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
      if is_complete () then
        failwith "Commands after End are not allowed in a .thmod" ;
      if current_name () = None then
        failwith "A .thmod must start with a Module command"

let remove_scope_declarations sc =
  let names =
    List.map (fun item -> item.item_name) sc.sc_items
  in
  let (ktable, ctable) = !sign in
  sign :=
    (List.filter (fun (id, _) -> not (List.mem id names)) ktable,
     List.filter (fun (id, _) -> not (List.mem id names)) ctable) ;
  Prover.remove_globals names

let process_module name params =
  let is_top = current_name () = None in
  if is_top then begin
    if is_complete () then
      failwith "Module after End is not allowed in a .thmod" ;
    let base = basename () in
    if name <> base then
      failwithf "Module %s does not match the file name %s.thmod"
        name base
  end ;
  push_frame !sr ;
  enter_module name params

let process_end name =
  let closed, is_top = leave_module ~retain_top:false name in
  if not is_top then remove_scope_declarations closed ;
  sr := pop_frame ()
