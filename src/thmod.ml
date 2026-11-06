(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                            en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Module scopes, instances, name resolution, Module/End handling, and
   the .thmodc codec for reasoning-level modules. Internal names are
   stored relative to the top-level module: a direct item is [x], and an
   item in the nested module [Bar] is [Bar.x]. *)

open Term
open Typing
open Metaterm
open Abella_types
open Extensions

module Setup = Driver_setup

let read source =
  Source.read_compiled ~suffix:".thmod" ~compiled_suffix:".thmodc" source

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
  en_instances : (string * instance) list ; (* top-level .thm imports *)
  en_complete : bool ;
}

let initial_env = {
  en_stack = [] ;
  en_top = None ;
  en_templates = [] ;
  en_instances = [] ;
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
  | None -> List.assoc_opt name !env.en_instances
  | Some sc -> List.assoc_opt name sc.sc_instances

let add_instance inst =
  match !env.en_stack with
  | [] ->
      if List.mem_assoc inst.ins_name !env.en_instances then
        failwithf "Module name %s is already imported" inst.ins_name ;
      env := { !env with
               en_instances =
                 !env.en_instances @ [(inst.ins_name, inst)] }
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
  List.flatten_map (fun sc -> List.map snd sc.sc_instances) !env.en_stack @
  List.map snd !env.en_instances

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
  let instances = List.map fst !env.en_instances in
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
  List.unique (templates @ instances @ names)

let all_child_names () =
  match current_scope () with
  | None -> List.map fst !env.en_instances
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

let sign_of_content content =
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

module Spec : Artifact.SPEC with type t = artifact = struct
  type t = artifact

  let file_kind = `thmod
  let suffix = ".thmod"
  let compiled_suffix = ".thmodc"
  let compiling_key ~modname = modname ^ ".thmod"

  let extract () =
    let name = match top_name () with
      | Some name -> name
      | None -> failwith "Cannot write a .thmodc without a module"
    in
    let content = exported_content () in
    { ta_name = name ;
      ta_params = top_params () ;
      ta_content = content ;
      ta_nested = nested_module_names () ;
      ta_exports = exported_names () ;
    }

  let encode art =
    let sign = sign_of_content art.ta_content in
    let predicates =
      Artifact.predicates sign |>
      List.filter (fun id -> List.mem id art.ta_exports)
    in
    [
      Obj.repr art.ta_name ;
      Obj.repr art.ta_params ;
      Obj.repr sign ;
      Obj.repr !Setup.spec_clauses ;
      Obj.repr predicates ;
      Obj.repr art.ta_content ;
      Obj.repr art.ta_nested ;
      Obj.repr art.ta_exports ;
    ]

  let decode read =
    let name = (Obj.obj (read ()) : string) in
    let params = (Obj.obj (read ()) : string list) in
    ignore (Obj.obj (read ()) : Typing.sign) ;
    ignore (Obj.obj (read ()) : clause list) ;
    ignore (Obj.obj (read ()) : string list) ;
    let content = (Obj.obj (read ()) : compiled list) in
    let nested = (Obj.obj (read ()) : string list) in
    let exports = (Obj.obj (read ()) : string list) in
    { ta_name = name ;
      ta_params = params ;
      ta_content = content ;
      ta_nested = nested ;
      ta_exports = exports ;
    }
end

module Codec = Artifact.Make (Spec)

let write_compilation () =
  match !Setup.compiled with
  | None -> ()
  | Some compiled -> Codec.write_compiled compiled

(* File structure *)

let is_complete () = (!env).en_complete

let basename () =
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

let check_structure cmd =
  match !Setup.file_kind with
  | `thm ->
      if current_name () <> None then check_module_body cmd
  | `thmod ->
      check_thmod_structure cmd

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
  match !Setup.file_kind with
  | `thm ->
      if current_name () = None && find_instance name <> None then
        failwithf "Module name %s is already imported" name ;
      push_frame !sr ;
      enter_module ~top_path:[name] name params
  | `thmod ->
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
  let retain_top = !Setup.file_kind = `thm in
  let closed, is_top = leave_module ~retain_top name in
  if retain_top || not is_top then remove_scope_declarations closed ;
  sr := pop_frame ()

(* Import Module and Show Module orchestration, plus the pure
   transformations used when instantiating an imported reasoning
   module. *)

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

let in_module () = current_name () <> None

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
  | TargetTemplate of template
  | TargetInstance of instance

type resolved_key = {
  rk_source : string ;
  rk_prefixed : string ;
  rk_predicate : bool ;
}

let resolve_import_target ~(load : modname:string -> artifact) mi =
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
        tp_name = artifact.ta_name ;
        tp_from = [] ;
        tp_source = source ;
        tp_params = artifact.ta_params ;
        tp_content = artifact.ta_content ;
        tp_nested = artifact.ta_nested ;
      } in
      (TargetTemplate template, artifact.ta_name, source)
  | NameSource name ->
      let template = find_template name in
      let instance = find_instance name in
      if mi.mi_tyargs <> [] then
        begin match template with
        | Some template ->
            (TargetTemplate template, name, template.tp_source)
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
            (TargetInstance instance, name, instance.ins_source)
        | None ->
            begin match template with
            | Some template ->
                (TargetTemplate template, name, template.tp_source)
            | None -> failwithf "Unknown module %s" name
            end
        end

let resolve_type_args args =
  List.map begin fun ty ->
    let ty = if in_module () then resolve_ty ty else ty in
    kind_check !sign ty ;
    if Checks.contains_prop ty then
      failwithf "Type argument %s may not contain prop"
        (ty_to_string ty) ;
    let free = get_typaram ty in
    if in_module () then begin
      let allowed = all_params () in
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
  let rigid = rigid_predicates_of_decls rigid_decls in
  (renamer, materialized, rigid)

let value_of_item item =
  match item.item_class with
  | PredicateItem | DefineItem ->
      begin match item.item_ty with
      | Some ty ->
          PredValue {
            pv_name = item.item_name ;
            pv_typarams = item.item_typarams ;
            pv_ty = ty ;
          }
      | None -> failwithf "Missing type for predicate %s"
                  item.item_name
      end
  | AxiomItem | TheoremItem ->
      let (tys, stmt) = Prover.get_generic_lemma item.item_name in
      let tag = Prover.get_lemma_tag item.item_name in
      AxiomValue {
        av_name = item.item_name ;
        av_typarams = tys ;
        av_stmt = stmt ;
        av_tag = tag ;
      }
  | KindItem | TypeItem ->
      failwithf "%s is not a predicate or axiom"
        item.item_name

let value_of_name ~predicate name =
  let local_name () =
    let name = resolve_id name in
    match lookup_item_by_name name with
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
          match class_of_compiled decl with
          | Some PredicateItem -> true
          | Some AxiomItem -> false
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
              if Checks.contains_prop_argument ty then
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
    ~(load : modname:string -> artifact) ~record mi =
  let target, default_name, source = resolve_import_target ~load mi in
  let name = match mi.mi_alias with
    | Some alias -> alias
    | None -> default_name
  in
  if List.mem name (all_params ()) then
    failwithf "Module name %s is already used as a module parameter" name ;
  begin match mi.mi_alias with
  | None ->
      if find_instance name <> None then
        failwithf "Module %s has already been imported" name
  | Some alias ->
      if find_instance alias <> None then
        failwithf "Module name %s is already imported" alias ;
      if find_template alias <> None then
        failwithf "Module name %s is already in use" alias
  end ;
  let prefix = instance_prefix name in
  let source_decls, from, params, args, is_instance =
    match target with
    | TargetTemplate template ->
        let args = resolve_type_args mi.mi_tyargs in
        if List.length args <> List.length template.tp_params then
          failwithf "Module %s expects %d type arguments but got %d"
            template.tp_name
            (List.length template.tp_params)
            (List.length args) ;
        (template.tp_content, template.tp_from,
         template.tp_params, args, false)
    | TargetInstance instance ->
        if mi.mi_tyargs <> [] then
          failwithf "Module %s is already instantiated"
            instance.ins_name ;
        (instance.ins_decls, instance.ins_prefix,
         [], [], true)
  in
  let args =
    match target with
    | TargetTemplate _ -> args
    | TargetInstance instance -> instance.ins_tyargs
  in
  let renamer, materialized, rigid =
    materialize_import ~decls:source_decls ~from ~to_:prefix
      ~params ~args ~is_instance ~avoid:(all_params ())
  in
  let rigid =
    List.fold_left begin fun rigid instance ->
      if instance.ins_source = source then
        Iset.union rigid
          (rigid_predicates_of_decls instance.ins_decls)
      else
        rigid
    end rigid (all_instances ())
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
    ins_name = name ;
    ins_source = source ;
    ins_prefix = prefix ;
    ins_decls = final ;
    ins_tyargs = args ;
  } in
  add_instance instance ;
  Output.msg_printf "Imported module %s." name

let show_module ~(load : modname:string -> artifact) src =
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
        begin match find_instance name with
        | Some instance ->
            (instance.ins_name, [], instance.ins_prefix,
             instance.ins_decls)
        | None ->
            begin match find_template name with
            | Some template ->
                (template.tp_name, template.tp_params,
                 template.tp_from, template.tp_content)
            | None ->
                if List.mem name (all_params ()) then
                  failwithf "Module parameter %s is not a module" name ;
                failwithf "Unknown module %s" name
            end
        end
  in
  let summary =
    summary_to_string ~name ~params ~prefix content in
  Output.msg_printf "%s" summary
