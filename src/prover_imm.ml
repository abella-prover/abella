(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2022 Inria (Institut National de Recherche            *)
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
open Typing
open Metaterm
open Tactics
open Checks
open Abella_types
open Extensions
open Unifyty

(* Sequent *)

type hyp = {
  id : id ;
  term : metaterm ;
  abbrev : string option ;
  user_named : bool ;
}

(* [activate] restores the global [Term] bind state (plus the
   schematic instantiations) captured for this subgoal. The
   input to every tactic is assumed activated; of the
   returned subgoals the first is active ([activate] is a
   no-op) and the rest are inactive. The scheduler calls
   [activate_sequent] before focusing an inactive subgoal. *)
type sequent = {
  vars : (id * term) list ;
  user_vars : Iset.t ;
  hyps : hyp list ;
  goal : metaterm ;
  count : int ;
  name : string ;
  next_subgoal_id : int ;
  active : bool ;
  activate : unit -> unit ;
}

let noop () = ()

let empty_sequent goal =
  { vars = [] ; user_vars = Iset.empty ; hyps = [] ; goal ;
    count = 0 ; name = "" ; next_subgoal_id = 1 ;
    active = true ; activate = noop }

(* [keep_active sq sq'] preserves activation for tactics with
   a single outcome: the result stays focused, so the global
   bind state already corresponds to it. *)
let keep_active sq sq' =
  { sq' with active = sq.active ; activate = sq.activate }

let activate_sequent sq =
  if sq.active then sq
  else begin
    sq.activate () ;
    { sq with active = true ; activate = noop }
  end

(* Mirror of [Prover.add_subgoals] naming: several subgoals
   are numbered from [next_subgoal_id]; a single subgoal
   keeps its name. *)
let name_subgoals base subs =
  match subs with
  | [] | [_] -> subs
  | _ ->
      List.mapi
        (fun i sq ->
          let idx = base.next_subgoal_id + i in
          let name =
            if base.name = "" then string_of_int idx
            else base.name ^ "." ^ string_of_int idx
          in
          { sq with name ; next_subgoal_id = 1 })
        subs

let normalize_sequent sq =
  { sq with
    goal = normalize sq.goal ;
    hyps = List.map (fun h -> { h with term = normalize h.term })
        sq.hyps }

(* Pure sequent helpers *)

let fresh_hyp_name sq base =
  if base = "" then ({ sq with count = sq.count + 1 },
                     "H" ^ string_of_int (sq.count + 1))
  else (sq, fresh_name base
              (List.map (fun h -> (h.id, ())) sq.hyps))

let update_hyp_count sq name =
  if name = "" || name.[0] <> 'H' then sq
  else match int_of_string (String.sub name 1 (String.length name - 1)) with
  | n -> { sq with count = max sq.count n }
  | exception _ -> sq

let unsafe_add_hyp sq ?(user_named = false) name term =
  { sq with
    hyps = sq.hyps
           @ [{ id = name ; term ; abbrev = None ; user_named }] }

let add_auto_hyp sq ?(base = "") term =
  let sq, name = fresh_hyp_name sq base in
  unsafe_add_hyp (update_hyp_count sq name) name term

let add_hyp sq ?name term =
  match name with
  | None -> add_auto_hyp sq term
  | Some name ->
      let sq, name = fresh_hyp_name sq name in
      unsafe_add_hyp (update_hyp_count sq name)
        ~user_named:true name term

let add_named_hyp sq base term =
  let used =
    List.map (fun (x, _) -> (x, ())) sq.vars
    @ List.map (fun h -> (h.id, ())) sq.hyps
  in
  let name = fresh_name base used in
  unsafe_add_hyp (update_hyp_count sq name)
    ~user_named:true name term

let add_hyps_with_hint sq ?(auto_base = "") alt hyps =
  let _, sq =
    List.fold_left
      (fun (i, sq) hyp ->
        let hint =
          Option.bind alt (fun a -> Prover.name_hint_at a.hspec_hyps i)
        in
        let sq =
          match hint with
          | Some base -> add_named_hyp sq base hyp
          | None -> add_auto_hyp sq ~base:auto_base hyp
        in
        (i + 1, sq))
      (0, sq) hyps
  in
  sq

let add_hyp_with_hint sq alt term = add_hyps_with_hint sq alt [term]

let add_var sq ?(user = false) ((name, _) as v) =
  let sq = { sq with vars = sq.vars @ [v] } in
  if user then { sq with user_vars = Iset.add name sq.user_vars }
  else sq

let add_if_new_var sq ?(user = false) ((name, _) as v) =
  if List.mem_assoc name sq.vars then sq else add_var sq ~user v

let replace_hyp sq name t =
  { sq with
    hyps = List.map
        (fun h -> if h.id = name then { h with term = t } else h)
        sq.hyps }

let nominal_vars_of_sequent sq =
  let terms =
    collect_terms sq.goal
    @ List.flatten_map (fun h -> collect_terms h.term) sq.hyps
  in
  find_var_refs Nominal terms |> List.map term_to_var

let update_self_bound_vars sq =
  { sq with
    vars = List.map
        (fun (id, term) ->
          match term_head term with
          | Some (v, _) when term_to_name v = id -> (id, v)
          | _ -> (id, term))
        sq.vars }

(* Statement resolution (pure variant of [Prover.get_stmt_clearly]) *)

type stmt_error =
  | Unknown_stmt of string
  | Extrude_unknown of id
  | Lemma_arity of { name : string ; expected : int ; got : int }
  | Lemma_prop_arg of string

let get_hyp sq name =
  List.find_opt (fun h -> h.id = name) sq.hyps
  |> Option.map (fun h -> h.term)

let is_hyp sq name = Option.is_some (get_hyp sq name)

let get_lemma ?(tys : ty list = []) name
    : (metaterm, stmt_error) result =
  match Hashtbl.find_opt Prover.lemmas name with
  | None -> Result.error (Unknown_stmt name)
  | Some (argtys, bod) ->
      let tys =
        if List.length argtys > 0 && List.length tys = 0 then
          List.map (fun _ -> fresh_tyvar ()) argtys
        else tys
      in
      if List.length tys <> List.length argtys then
        Result.error
          (Lemma_arity
             { name ; expected = List.length argtys ;
               got = List.length tys })
      else if List.exists contains_prop tys then
        Result.error (Lemma_prop_arg name)
      else
        let tysub = List.map2 (fun id ty -> (id, ty)) argtys tys in
        mark_schematic_tysub tysub ;
        Result.ok (map_on_tys (apply_sub_ty tysub) bod)

let get_hyp_or_lemma sq ?(tys : ty list = []) name =
  match get_hyp sq name with
  | Some t -> Result.ok t
  | None -> get_lemma ~tys name

(* [Remove (h, [])] on a hypothesis deletes it and returns
   the updated sequent alongside the statement. *)
let get_stmt_clearly sq h
    : ((sequent * metaterm), stmt_error) result =
  match h with
  | Keep (h, tys) ->
      get_hyp_or_lemma sq ~tys h |> Result.map (fun t -> (sq, t))
  | Remove (h, []) when is_hyp sq h ->
      let stmt = Option.get (get_hyp sq h) in
      let sq =
        { sq with hyps = List.filter (fun hh -> hh.id <> h) sq.hyps }
      in
      Result.ok (sq, stmt)
  | Remove (h, tys) -> get_lemma ~tys h |> Result.map (fun t -> (sq, t))

let get_arg_clearly sq = function
  | Keep ("_", _) -> Result.ok (sq, None)
  | arg ->
      get_stmt_clearly sq arg
      |> Result.map (fun (sq, t) -> (sq, Some t))

(* Renaming (pure) *)

type rename_hint_error =
  | Bad_nominal_hint of string
  | Nominal_in_use of string
  | Reserved_nominal_hint of string

let rename_described sq ~hints ~base vars
    : (sequent, rename_hint_error) result =
  let used =
    ref (List.map (fun (name, _) -> (name, ())) base.vars
         @ List.map (fun h -> (h.id, ())) sq.hyps
         @ List.map (fun (v : var) -> (v.name, ()))
             (nominal_vars_of_sequent sq))
  in
  let rec collect i acc = function
    | [] -> Result.ok (List.rev acc)
    | ((old_var : var), in_sequent) :: rest -> begin
        match Prover.name_hint_at hints i with
        | None ->
            used := (old_var.name, ()) :: !used ;
            collect (i + 1) acc rest
        | Some base_name ->
            let new_name =
              if old_var.tag = Nominal then
                if not (is_nominal_name base_name) then
                  Result.error (Bad_nominal_hint base_name)
                else
                  let used_for_hint =
                    List.remove_assoc old_var.name !used
                  in
                  if List.mem_assoc base_name used_for_hint then
                    Result.error (Nominal_in_use base_name)
                  else Result.ok base_name
              else if is_nominal_name base_name then
                Result.error (Reserved_nominal_hint base_name)
              else Result.ok (fresh_name base_name !used)
            in
            begin match new_name with
            | Result.Error _ as e -> e
            | Result.Ok new_name ->
                used := (new_name, ()) :: !used ;
                let new_var =
                  var old_var.tag new_name old_var.ts old_var.ty
                in
                collect (i + 1)
                  ((old_var.tag, old_var.name, new_name, new_var,
                    in_sequent)
                   :: acc)
                  rest
            end
      end
  in
  match collect 0 [] vars with
  | Result.Error _ as e -> e
  | Result.Ok [] -> Result.ok sq
  | Result.Ok renames ->
      let tag_groups =
        List.fold_left
          (fun groups (tag, old_name, _, new_var, _) ->
            let old =
              try List.assoc tag groups with Not_found -> []
            in
            (tag, (old_name, new_var) :: old)
            :: List.remove_assoc tag groups)
          [] renames
      in
      let rewrite_term term =
        List.fold_left
          (fun term (tag, alist) -> replace_term_vars ~tag alist term)
          term tag_groups
      in
      let rewrite_metaterm mt =
        List.fold_left
          (fun mt (tag, alist) -> replace_metaterm_vars ~tag alist mt)
          mt tag_groups
      in
      Result.ok
        { sq with
          goal = rewrite_metaterm sq.goal ;
          hyps = List.map
              (fun h -> { h with term = rewrite_metaterm h.term })
              sq.hyps ;
          vars = List.map
              (fun (name, term) ->
                let name =
                  match List.find_opt
                      (fun (_, old_name, _, _, in_sequent) ->
                        in_sequent && old_name = name)
                      renames with
                  | Some (_, _, new_name, _, _) -> new_name
                  | None -> name
                in
                (name, rewrite_term term))
              sq.vars ;
          user_vars = List.fold_left
              (fun user_vars
                (_, old_name, new_name, _, in_sequent) ->
                if in_sequent then
                  Iset.add new_name (Iset.remove old_name user_vars)
                else user_vars)
              sq.user_vars renames }

let rename_new_vars sq ?alt ~base ()
    : (sequent, rename_hint_error) result =
  let hints =
    match alt with None -> [] | Some a -> a.hspec_vars
  in
  if hints = [] then Result.ok sq
  else
    let new_eigen =
      List.filter
        (fun (name, term) ->
          (not (List.mem_assoc name base.vars)) && is_free term)
        sq.vars
    in
    let new_eigen_names = List.map fst new_eigen in
    let base_nominals =
      List.map (fun (v : var) -> v.name)
        (nominal_vars_of_sequent base)
    in
    let new_nominals =
      nominal_vars_of_sequent sq
      |> List.filter (fun (v : var) ->
          (not (List.mem v.name base_nominals))
          && not (List.mem v.name new_eigen_names))
    in
    let described =
      List.map (fun (_, term) -> (term_to_var term, true)) new_eigen
      @ List.map (fun (v : var) -> (v, false)) new_nominals
    in
    rename_described sq ~hints ~base described

(* Shared guards *)

(* Map the [is_tactic_failure] exception set to a bespoke
   error at the tactic boundary; anything else (bugs,
   interrupts) keeps propagating. *)
let tactic_failure_message = function
  | Failure msg -> Some msg
  | Unify.UnifyFailure fl ->
      Some (Unify.explain_failure fl)
  | Unify.UnifyError err -> Some (Unify.explain_error err)
  | Unifyty.InstGenericTyvar (v, ty) ->
      Some
        (Unify.explain_error (Unify.InstGenericTyvar (v, ty)))
  | TypeInferenceFailure (exp, act, _) ->
      Some
        (Printf.sprintf "expected %s but got %s"
           (ty_to_string exp) (ty_to_string act))
  | _ -> None

let map_tactic_failure mk f =
  try f ()
  with e -> begin
    match tactic_failure_message e with
    | Some msg -> Result.error (mk msg)
    | None -> raise e
  end

let next_restriction sq =
  1
  + (sq.hyps |> List.map (fun h -> h.term)
     |> List.map get_max_restriction |> List.max)

let rec nth_product n term =
  match term with
  | Binding (Forall, _, body) -> nth_product n body
  | Binding (Nabla, _, body) -> nth_product n body
  | Arrow (left, right) ->
      if n = 1 then Result.ok left else nth_product (n - 1) right
  | _ -> Result.error "Can only induct on predicates and judgments"

(* Induction *)

type induction_error =
  | Coinductive_goal
  | Arity_mismatch of { expected : int ; got : int }
  | Not_inductive of string
  | Bad_induction_target of string
  | Induction_tactic_failure of string

let ensure_is_inductive term =
  match term with
  | Obj _ -> Result.ok ()
  | Pred (p, _) ->
      let pname = term_head_name p in
      begin match Hashtbl.find_opt Prover.defs_table pname with
      | Some { flavor = Inductive ; _ } -> Result.ok ()
      | Some { flavor = CoInductive ; _ } ->
          Result.error (Not_inductive
                          ("Cannot induct on " ^ pname
                           ^ " since it has been coinductively defined"))
      | None ->
          Result.error (Not_inductive
                          ("Cannot induct on " ^ pname
                           ^ " since it has not been defined"))
      end
  | _ -> Result.error (Bad_induction_target
                         "Can only induct on predicates and judgments")

let induction sq ?hint ind_args
    : (sequent, induction_error) result =
  if has_coinductive_restriction sq.goal then
    Result.error Coinductive_goal
  else
    let stmts = and_to_list sq.goal in
    if List.length ind_args <> List.length stmts then
      Result.error
        (Arity_mismatch
           { expected = List.length stmts ; got = List.length ind_args })
    else
      let check =
        List.combine ind_args stmts
        |> List.fold_left
          (fun acc (arg, goal) ->
            match acc with
            | Result.Error _ as e -> e
            | Result.Ok () -> begin
                match nth_product arg goal with
                | Result.Error msg ->
                    Result.error (Bad_induction_target msg)
                | Result.Ok t -> ensure_is_inductive t
              end)
          (Result.ok ())
      in
      begin match check with
      | Result.Error _ as e -> e
      | Result.Ok () ->
          map_tactic_failure
            (fun msg -> Induction_tactic_failure msg)
            (fun () ->
              let res_num = next_restriction sq in
              let ihs, new_goal =
                Tactics.induction ind_args res_num sq.goal
              in
              let sq =
                add_hyps_with_hint sq ~auto_base:"IH"
                  (Prover.alt_for_subgoal hint 0) ihs
              in
              Result.ok (keep_active sq { sq with goal = new_goal }))
      end

(* Coinduction *)

type coinduction_error =
  | Inductive_inside
  | Not_coinductive of string
  | Bad_coinduction_target of string
  | Coinduction_tactic_failure of string

let rec conclusion term =
  match term with
  | Binding (Forall, _, body) -> conclusion body
  | Binding (Nabla, _, body) -> conclusion body
  | Arrow (_left, right) -> conclusion right
  | Pred (p, _) -> Result.ok p
  | _ -> Result.error "Cannot coinduct on a goal of this form"

let ensure_is_coinductive p =
  let pname = term_head_name p in
  match Hashtbl.find_opt Prover.defs_table pname with
  | Some { flavor = CoInductive ; _ } -> Result.ok ()
  | Some { flavor = Inductive ; _ } ->
      Result.error (Not_coinductive
                      ("Cannot coinduct on " ^ pname
                       ^ " since it has been inductively defined"))
  | None ->
      Result.error (Not_coinductive
                      ("Cannot coinduct on " ^ pname
                       ^ " since it has not been defined"))

let coinduction sq ?hint ()
    : (sequent, coinduction_error) result =
  match conclusion sq.goal with
  | Result.Error msg -> Result.error (Bad_coinduction_target msg)
  | Result.Ok p -> begin
      match ensure_is_coinductive p with
      | Result.Error _ as e -> e
      | Result.Ok () ->
          if has_inductive_restriction sq.goal then
            Result.error Inductive_inside
          else
            map_tactic_failure
              (fun msg -> Coinduction_tactic_failure msg)
              (fun () ->
                let res_num = next_restriction sq in
                let ch, new_goal =
                  Tactics.coinduction res_num sq.goal
                in
                let sq =
                  add_hyps_with_hint sq ~auto_base:"CH"
                    (Prover.alt_for_subgoal hint 0) [ch]
                in
                Result.ok (keep_active sq { sq with goal = new_goal }))
    end

(* Intros *)

type intros_error = Intros_rename of rename_hint_error

let intros sq alt : (sequent, intros_error) result =
  let base = sq in
  let rec aux sq intro_vars hyp_index term =
    match term with
    | Binding (Forall, bindings, body) ->
        let support = metaterm_support body in
        let alist, vars =
          fresh_raised_alist ~sr:!sr ~tag:Eigen ~used:sq.vars
            ~support bindings
        in
        let intro_vars =
          intro_vars
          @ List.map (fun v -> (term_to_var v, true)) vars
        in
        let sq =
          List.fold_left
            (fun sq v -> add_var sq (term_to_pair v))
            sq vars
        in
        aux sq intro_vars hyp_index
          (replace_metaterm_vars alist body)
    | Binding (Nabla, bindings, body) ->
        let ids, tys = List.split bindings in
        let nominals = fresh_nominals tys body in
        let intro_vars =
          intro_vars
          @ List.map (fun t -> (term_to_var t, false)) nominals
        in
        aux sq intro_vars hyp_index
          (replace_metaterm_vars (List.combine ids nominals) body)
    | Arrow (left, right) ->
        let hint = Prover.name_hint_at alt.hspec_hyps hyp_index in
        let sq =
          match hint with
          | Some b -> add_named_hyp sq b (normalize left)
          | None -> add_auto_hyp sq (normalize left)
        in
        aux sq intro_vars (hyp_index + 1) right
    | _ -> (sq, intro_vars, term)
  in
  let sq, intro_vars, goal = aux sq [] 0 sq.goal in
  let sq = keep_active sq { sq with goal } in
  rename_described sq ~hints:alt.hspec_vars ~base intro_vars
  |> Result.map_error (fun e -> Intros_rename e)

(* Search helpers (pure variants operating on an explicit sequent) *)

let has_inductive_hyps hyp =
  let rec aux term =
    match term with
    | Binding (Forall, _, body) -> aux body
    | Binding (Nabla, _, body) -> aux body
    | Arrow (Obj (_, Smaller _), _) -> true
    | Arrow (Pred (_, Smaller _), _) -> true
    | Arrow (_left, right) -> aux right
    | _ -> false
  in
  aux hyp.term

let remove_inductive_hypotheses hyps =
  List.remove_all has_inductive_hyps hyps

let has_coinductive_result hyp =
  let rec aux term nested =
    match term with
    | Binding (Forall, _, body) -> aux body true
    | Binding (Nabla, _, body) -> aux body true
    | Arrow (_left, right) -> aux right true
    | Pred (_, CoSmaller _) -> nested
    | Pred (_, CoEqual _) -> nested
    | _ -> false
  in
  aux hyp.term false

let remove_coinductive_hypotheses hyps =
  List.remove_all has_coinductive_result hyps

let retype sq t = type_uterm ~sr:!sr ~sign:!sign ~ctx:sq.vars t

let search_goal_witness sq ?depth goal witness =
  let hyps =
    sq.hyps |> remove_inductive_hypotheses
    |> remove_coinductive_hypotheses
    |> List.map (fun h -> (h.id, h.term))
  in
  let depth = Option.value ~default:!Prover.search_depth depth in
  Tactics.search ~depth ~hyps ~clauses:!Prover.clauses
    ~def_unfold:Prover.def_unfold ~sr:!sr ~retype:(retype sq)
    ~witness goal

let search_goal sq ?depth goal =
  try Option.is_some (search_goal_witness sq ?depth goal WMagic)
  with Failure _ -> false

(* Split *)

type split_error = Needless_split

let split sq propagate_result
    : (sequent list, split_error) result =
  let conjs = and_to_list sq.goal in
  if List.length conjs = 1 then Result.error Needless_split
  else
    let rec build prev acc = function
      | [] -> List.rev acc
      | g :: rest ->
          let core =
            if propagate_result then
              List.fold_left
                (fun sq h -> add_auto_hyp sq h)
                { sq with goal = g } (List.rev prev)
            else { sq with goal = g }
          in
          build (g :: prev) (core :: acc) rest
    in
    let schem = !Term.schematic_instantiations in
    let bs = Term.get_bind_state () in
    build [] [] conjs |> name_subgoals sq
    |> List.mapi (fun i core ->
        if i = 0 then { core with active = true ; activate = noop }
        else
          { core with
            active = false ;
            activate =
              (fun () ->
                Term.set_bind_state bs ;
                Term.schematic_instantiations := schem) })
    |> Result.ok

(* Left / right. The mutable versions are silent no-ops off
   disjunction; here that is a bespoke error. *)

type disjunction_error = Not_disjunction

let left sq : (sequent, disjunction_error) result =
  match sq.goal with
  | Or (l, _) -> Result.ok (keep_active sq { sq with goal = l })
  | _ -> Result.error Not_disjunction

let right sq : (sequent, disjunction_error) result =
  match sq.goal with
  | Or (_, r) -> Result.ok (keep_active sq { sq with goal = r })
  | _ -> Result.error Not_disjunction

(* Existential witness *)

type exists_error =
  | Not_existential
  | Unresolvable_witness of string
  | Exists_type_error of string

let rec resolve_ewitness ew tids =
  match ew, tids with
  | ETerm t, (id, ty) :: tids -> Result.ok (id, ty, t, tids)
  | ESub (x, t), (id, ty) :: tids ->
      if x = id then Result.ok (x, ty, t, tids)
      else
        resolve_ewitness ew tids
        |> Result.map (fun (_, xty, _, rest) ->
            (x, xty, t, (id, ty) :: rest))
  | _, [] ->
      Result.error
        (Unresolvable_witness (ewitness_to_string ew))

let exists_tac sq ew : (sequent, exists_error) result =
  match sq.goal with
  | Binding (Metaterm.Exists, tids, body) -> begin
      match resolve_ewitness ew tids with
      | Result.Error _ as e -> e
      | Result.Ok (id, ty, t, tids) ->
          let ntids = metaterm_nominal_tids body in
          let ctx =
            sq.vars
            @ List.map
                (fun (id, ty) -> (id, nominal_var id ty))
                ntids
          in
          begin try
            let t =
              type_uterm ~expected_ty:ty ~sr:!sr ~sign:!sign ~ctx t
            in
            let goal =
              replace_metaterm_vars [(id, t)]
                (Metaterm.exists tids body)
            in
            Result.ok
              (normalize_sequent (keep_active sq { sq with goal }))
          with
          | TypeInferenceFailure (exp, act, _) ->
              Result.error
                (Exists_type_error
                   (Printf.sprintf "expected %s but got %s"
                      (ty_to_string exp) (ty_to_string act)))
          | Failure msg -> Result.error (Exists_type_error msg)
          end
    end
  | _ -> Result.error Not_existential

(* Clear *)

type clear_error =
  | Unknown_label of id
  | Strict_var_in_use of id
  | Extrude_unknown of id

let is_used sq v =
  List.exists
    (fun h ->
      get_metaterm_used h.term
      |> List.exists (fun xv -> fst xv = v))
    sq.hyps

let check_removable sq h =
  if is_hyp sq h then Result.ok ()
  else begin
    match List.assoc_opt h sq.vars with
    | None -> Result.error (Unknown_label h)
    | Some v ->
        if is_uninstantiated (h, v) && is_used sq h then
          Result.error (Strict_var_in_use h)
        else Result.ok ()
  end

let remove_hyp sq cm name
    : (sequent, clear_error) result =
  let removed = List.find_opt (fun h -> h.id = name) sq.hyps in
  let sq =
    { sq with hyps = List.filter (fun h -> h.id <> name) sq.hyps }
  in
  match cm, removed with
  | Clear_extro, Some h ->
      Result.ok { sq with goal = Arrow (h.term, sq.goal) }
  | Clear_extro, None -> Result.error (Extrude_unknown name)
  | _ -> Result.ok sq

let remove_var sq cm h : (sequent, clear_error) result =
  match List.assoc_opt h sq.vars with
  | None -> Result.error (Unknown_label h)
  | Some tm ->
      let v = term_to_var tm in
      let sq =
        { sq with
          vars = List.filter (fun xv -> fst xv <> h) sq.vars ;
          user_vars = Iset.remove h sq.user_vars }
      in
      begin match cm with
      | Clear_extro ->
          let goal =
            replace_metaterm_vars
              [h, var Constant v.Term.name v.ts v.ty]
              sq.goal
          in
          Result.ok
            { sq with goal = forall [v.Term.name, v.ty] goal }
      | _ -> Result.ok sq
      end

let remove_thing sq cm h =
  if is_hyp sq h then remove_hyp sq cm h else remove_var sq cm h

let clear sq cm hs : (sequent, clear_error) result =
  List.fold_left
    (fun acc h ->
      match acc with
      | Result.Error _ as e -> e
      | Result.Ok sq -> begin
          match check_removable sq h with
          | Result.Error _ as e -> e
          | Result.Ok () -> remove_thing sq cm h
        end)
    (Result.ok sq) hs
  |> Result.map (keep_active sq)

(* Abbrev (infallible: no error type needed) *)

let abbrev sq ids str =
  keep_active sq
    { sq with
      hyps = List.map
          (fun h ->
            if Iset.mem h.id ids then { h with abbrev = Some str }
            else h)
          sq.hyps }

let unabbrev sq ids =
  keep_active sq
    { sq with
      hyps = List.map
          (fun h ->
            if Iset.mem h.id ids then { h with abbrev = None }
            else h)
          sq.hyps }

(* Duplicate hypothesis removal (infallible) *)

let clear_duplicates sq =
  let rec scan seen_preds acc = function
    | [] -> List.rev acc
    | (h : hyp) :: rest -> begin
        match h.term with
        | Pred (a, res) ->
            if List.exists
                (fun (oa, ores) -> res = ores && Term.eq a oa)
                seen_preds
            then scan seen_preds acc rest
            else scan ((a, res) :: seen_preds) (h :: acc) rest
        | _ -> scan seen_preds (h :: acc) rest
      end
  in
  keep_active sq { sq with hyps = scan [] [] sq.hyps }

(* Rename *)

type rename_error =
  | Lemma_clash of id
  | Hyp_clash of id
  | Var_clash of id
  | Unknown_rename_label of id

let rename_hyp sq hfr hto =
  { sq with
    hyps = List.map
        (fun h ->
          if h.id = hfr then { h with id = hto ; user_named = true }
          else h)
        sq.hyps }

let rename_var sq vfr xto : (sequent, rename_error) result =
  match List.assoc_opt vfr sq.vars with
  | None -> Result.error (Unknown_rename_label vfr)
  | Some tm ->
      let ty = tc [] tm in
      let vto = var Eigen xto 0 ty in
      let repl = [vfr, vto] in
      let rewrite mt = replace_metaterm_vars repl mt in
      Result.ok
        { sq with
          hyps = List.map
              (fun h -> { h with term = rewrite h.term })
              sq.hyps ;
          vars = List.filter_map
              (fun ((x, _) as v) ->
                if x = vfr then Some (xto, vto)
                else if x = xto then None
                else Some v)
              sq.vars ;
          user_vars = Iset.add xto (Iset.remove vfr sq.user_vars) ;
          goal = rewrite sq.goal }

let rename sq xfr xto : (sequent, rename_error) result =
  if Hashtbl.mem Prover.lemmas xto then
    Result.error (Lemma_clash xto)
  else if List.exists (fun h -> h.id = xto) sq.hyps then
    Result.error (Hyp_clash xto)
  else if
    match List.assoc_opt xto sq.vars with
    | Some t -> is_uninstantiated (xto, t)
    | None -> false
  then Result.error (Var_clash xto)
  else if List.exists (fun h -> h.id = xfr) sq.hyps then
    Result.ok (keep_active sq (rename_hyp sq xfr xto))
  else if List.mem_assoc xfr sq.vars then
    rename_var sq xfr xto |> Result.map (keep_active sq)
  else Result.error (Unknown_rename_label xfr)

(* Permute *)

type permute_error =
  | Not_a_permutation
  | Unknown_permute_hyp of id
  | Permute_tactic_failure of string

let permute sq ids form
    : (sequent, permute_error) result =
  if not (List.is_unique ids) then
    Result.error Not_a_permutation
  else
    let term =
      match form with
      | None -> Result.ok sq.goal
      | Some h -> begin
          match get_hyp sq h with
          | Some t -> Result.ok t
          | None -> Result.error (Unknown_permute_hyp h)
        end
    in
    match term with
    | Result.Error _ as e -> e
    | Result.Ok term ->
        map_tactic_failure
          (fun msg -> Permute_tactic_failure msg)
          (fun () ->
            let support_alist =
              List.map
                (fun t -> (term_to_name t, t))
                (metaterm_support term)
            in
            let perm =
              List.map
                (fun id ->
                  try List.assoc id support_alist
                  with Not_found ->
                    nominal_var id (tybase (atybase "")))
                ids
            in
            let result = Tactics.permute_nominals perm term in
            Result.ok
              (keep_active sq
                 (match form with
                  | None -> { sq with goal = result }
                  | Some hyp -> replace_hyp sq hyp result)))

(* Object-level instantiation *)

type inst_error =
  | Inst_stmt of stmt_error
  | Inst_not_object
  | Inst_nominal_not_in_support of id
  | Inst_type_error of string
  | Inst_tactic_failure of string

let inst sq ?hint h ws : (sequent, inst_error) result =
  match get_stmt_clearly sq h with
  | Result.Error e -> Result.error (Inst_stmt e)
  | Result.Ok (sq, ht) -> begin
      match ht with
      | Obj _ ->
          let rec aux sq ht = function
            | [] ->
                Result.ok
                  (add_hyp_with_hint sq
                     (Prover.alt_for_subgoal hint 0) ht)
            | (n, t) :: ws ->
                let ntids = metaterm_nominal_tids ht in
                begin match List.assoc_opt n ntids with
                | None ->
                    Result.error
                      (Inst_nominal_not_in_support n)
                | Some nty ->
                    let ctx =
                      sq.vars
                      @ List.map
                          (fun (id, ty) ->
                            (id, nominal_var id ty))
                          ntids
                    in
                    begin try
                      let t =
                        type_uterm ~expected_ty:nty ~sr:!sr
                          ~sign:!sign ~ctx t
                      in
                      aux sq (object_inst ht n t) ws
                    with
                    | TypeInferenceFailure (exp, act, _) ->
                        Result.error
                          (Inst_type_error
                             (Printf.sprintf "expected %s but got %s"
                                (ty_to_string exp)
                                (ty_to_string act)))
                    | Failure msg ->
                        Result.error (Inst_type_error msg)
                    end
                end
          in
          map_tactic_failure
            (fun msg -> Inst_tactic_failure msg)
            (fun () -> aux sq ht ws |> Result.map (keep_active sq))
      | _ -> Result.error Inst_not_object
    end

(* Object-level cut *)

type cut_error =
  | Cut_stmt of stmt_error
  | Cut_not_object
  | Cut_tactic_failure of string

let cut sq ?hint h arg : (sequent, cut_error) result =
  match get_stmt_clearly sq h with
  | Result.Error e -> Result.error (Cut_stmt e)
  | Result.Ok (sq, hstmt) -> begin
      match get_stmt_clearly sq arg with
      | Result.Error e -> Result.error (Cut_stmt e)
      | Result.Ok (sq, argstmt) -> begin
          match hstmt, argstmt with
          | Obj (obj_h, _), Obj (obj_arg, _) ->
              map_tactic_failure
                (fun msg -> Cut_tactic_failure msg)
                (fun () ->
                  Result.ok
                    (keep_active sq
                       (add_hyp_with_hint sq
                          (Prover.alt_for_subgoal hint 0)
                          (object_cut obj_h obj_arg))))
          | _ -> Result.error Cut_not_object
        end
    end

type cut_from_error =
  | Cut_from_stmt of stmt_error
  | Cut_from_not_object
  | Cut_from_type_error of string
  | Cut_from_tactic_failure of string

let cut_from sq ?hint h arg term
    : (sequent, cut_from_error) result =
  let term =
    try
      Result.ok
        (type_uterm ~sr:!sr ~sign:!sign ~ctx:sq.vars term)
    with
    | TypeInferenceFailure (exp, act, _) ->
        Result.error
          (Cut_from_type_error
             (Printf.sprintf "expected %s but got %s"
                (ty_to_string exp) (ty_to_string act)))
    | Failure msg -> Result.error (Cut_from_type_error msg)
  in
  match term with
  | Result.Error _ as e -> e
  | Result.Ok term -> begin
      match get_stmt_clearly sq h with
      | Result.Error e -> Result.error (Cut_from_stmt e)
      | Result.Ok (sq, hstmt) -> begin
          match get_stmt_clearly sq arg with
          | Result.Error e -> Result.error (Cut_from_stmt e)
          | Result.Ok (sq, argstmt) -> begin
              match hstmt, argstmt with
              | Obj (obj_h1, _), Obj (obj_h2, _) ->
                  map_tactic_failure
                    (fun msg -> Cut_from_tactic_failure msg)
                    (fun () ->
                      Result.ok
                        (keep_active sq
                           (add_hyp_with_hint sq
                              (Prover.alt_for_subgoal hint 0)
                              (object_cut_from obj_h1 obj_h2
                                 term))))
              | _, _ -> Result.error Cut_from_not_object
            end
        end
    end

(* Search cut *)

type search_cut_error =
  | Search_cut_stmt of stmt_error
  | Search_cut_not_object
  | Search_cut_tactic_failure of string

let search_cut sq ?hint h
    : (sequent, search_cut_error) result =
  match get_stmt_clearly sq h with
  | Result.Error e -> Result.error (Search_cut_stmt e)
  | Result.Ok (sq, ht) -> begin
      match ht with
      | Obj (obj, _) ->
          map_tactic_failure
            (fun msg -> Search_cut_tactic_failure msg)
            (fun () ->
              Result.ok
                (keep_active sq
                   (add_hyp_with_hint sq
                      (Prover.alt_for_subgoal hint 0)
                      (Obj
                         (Tactics.search_cut
                            ~search_goal:(search_goal sq) obj,
                          Irrelevant)))))
      | _ -> Result.error Search_cut_not_object
    end

(* Search: closing tactic, so the result is a subgoal list *)

type search_error =
  | Search_failed
  | Search_tactic_failure of string

let search sq ?depth ~witness ~handle_witness ()
    : (sequent list, search_error) result =
  match
    (try Result.ok (search_goal_witness sq ?depth sq.goal witness)
     with Failure msg ->
       Result.error (Search_tactic_failure msg))
  with
  | Result.Error _ as e -> e
  | Result.Ok None -> Result.error Search_failed
  | Result.Ok (Some w) ->
      handle_witness w ;
      Result.ok []

(* Assemble named subgoals from cores paired with the bind
   state each one owns. The first stays focused and its
   binds are installed globally, mirroring the trailing
   [Prover.next_subgoal] of branching tactics. With
   [~mainline:n], the last [n] cores are mainline
   continuations: like [Prover.add_subgoals ~mainline] they
   keep the base name (bumping [next_subgoal_id]) instead of
   being numbered. *)
let build_subgoals_full ?(mainline = 0) sq subs =
  let n_ob = List.length subs - mainline in
  let named =
    List.mapi
      (fun i (core, _, _) ->
        if mainline = 0 && n_ob <= 1 then core
        else if i < n_ob then
          let idx = sq.next_subgoal_id + i in
          let name =
            if sq.name = "" then string_of_int idx
            else sq.name ^ "." ^ string_of_int idx
          in
          { core with name ; next_subgoal_id = 1 }
        else
          { core with
            next_subgoal_id = sq.next_subgoal_id + n_ob })
      subs
  in
  let states =
    List.map (fun (_, bs, schem) -> (bs, schem)) subs
  in
  let result =
    List.mapi
      (fun i core ->
        if i = 0 then
          { core with active = true ; activate = noop }
        else
          let bs, schem = List.nth states i in
          { core with
            active = false ;
            activate =
              (fun () ->
                Term.set_bind_state bs ;
                Term.schematic_instantiations := schem) })
      named
  in
  begin match states with
  | [] -> result
  | (bs, schem) :: _ ->
      Term.set_bind_state bs ;
      Term.schematic_instantiations := schem ;
      result
  end

(* Attach activations to subgoal cores built under one bind
   state: the first stays focused, the rest go inactive.
   [name_subgoals] keeps driver order. *)
let build_subgoals sq schem bs cores =
  build_subgoals_full sq
    (List.map (fun core -> (core, bs, schem)) cores)

(* Apply *)

type apply_error =
  | Apply_stmt of stmt_error
  | Apply_unknown_with_var of id
  | Apply_type_error of string
  | Apply_restriction of string
  | Apply_logic_variable
  | Apply_rename of rename_hint_error
  | Apply_tactic_failure of string

let toplevel_bindings stmt =
  let rec aux = function
    | Binding (Forall, tids, t) -> tids @ aux t
    | Binding (Nabla, tids, t) -> tids @ aux t
    | _ -> []
  in
  aux stmt

let type_apply_withs sq stmt ws =
  List.fold_left
    (fun acc (id, t) ->
      match acc with
      | Result.Error _ as e -> e
      | Result.Ok typed -> begin
          match List.assoc_opt id (toplevel_bindings stmt) with
          | None ->
              Result.error (Apply_unknown_with_var id)
          | Some ty -> begin
              try
                let t =
                  type_uterm ~expected_ty:ty ~sr:!sr ~sign:!sign
                    ~ctx:sq.vars t
                in
                Result.ok (typed @ [(id, t)])
              with
              | TypeInferenceFailure (exp, act, _) ->
                  Result.error
                    (Apply_type_error
                       (Printf.sprintf "expected %s but got %s"
                          (ty_to_string exp) (ty_to_string act)))
              | Failure msg ->
                  Result.error (Apply_type_error msg)
            end
        end)
    (Result.ok []) ws

let check_no_restrictions term =
  let rec aux t nested =
    match t with
    | Binding (Forall, _, body) -> aux body true
    | Binding (Nabla, _, body) -> aux body true
    | Arrow (left, right) ->
        begin match aux left true with
        | Result.Error _ as e -> e
        | Result.Ok () -> aux right true
        end
    | Obj (_, Smaller _)
    | Obj (_, Equal _)
    | Pred (_, Smaller _)
    | Pred (_, Equal _) ->
        if nested then
          Result.error
            (Printf.sprintf
               "Inductive restrictions must not occur \
                in strict subterms:\n%s"
               (metaterm_to_string term))
        else Result.ok ()
    | Pred (_, CoSmaller _)
    | Pred (_, CoEqual _) ->
        Result.error
          "Co-Inductive restrictions must not be present"
    | _ -> Result.ok ()
  in
  aux term false

let has_logic_variable term =
  metaterm_vars_alist Logic term <> []

(* Partition obligations into those still needing proof and
   those discharged by search. Successful searches leave no
   bindings behind, so all remaining obligations share one
   bind state. *)
let partition_obligations sq ?depth obligations =
  List.fold_left
    (fun (left, right) g ->
      match search_goal_witness sq ?depth g WMagic with
      | Some w -> (left, (g, w) :: right)
      | None -> (g :: left, right))
    ([], []) obligations
  |> fun (left, right) -> (List.rev left, List.rev right)

let apply sq ?depth ?hint ?(term_witness = ignore) h args ws
    : (sequent list, apply_error) result =
  match get_stmt_clearly sq h with
  | Result.Error e -> Result.error (Apply_stmt e)
  | Result.Ok (sq, stmt) ->
      let rec resolve_args sq acc = function
        | [] -> Result.ok (sq, List.rev acc)
        | arg :: rest -> begin
            match get_arg_clearly sq arg with
            | Result.Error e -> Result.error (Apply_stmt e)
            | Result.Ok (sq, a) -> resolve_args sq (a :: acc) rest
          end
      in
      begin match resolve_args sq [] args with
      | Result.Error _ as e -> e
      | Result.Ok (sq, args) ->
          let restriction =
            List.fold_left
              (fun acc arg ->
                match acc with
                | Result.Error _ as e -> e
                | Result.Ok () -> begin
                    match arg with
                    | None -> Result.ok ()
                    | Some t -> begin
                        match check_no_restrictions t with
                        | Result.Error msg ->
                            Result.error
                              (Apply_restriction msg)
                        | Result.Ok () -> Result.ok ()
                      end
                  end)
              (Result.ok ()) args
          in
          begin match restriction with
          | Result.Error _ as e -> e
          | Result.Ok () -> begin
              match type_apply_withs sq stmt ws with
              | Result.Error _ as e -> e
              | Result.Ok ws ->
                  map_tactic_failure
                    (fun msg -> Apply_tactic_failure msg)
                    (fun () ->
                      let result, obligations =
                        Tactics.apply_with ~sr:!sr stmt args ws
                          ~used:(List.filter is_uninstantiated
                                   sq.vars)
                      in
                      let remaining, witnessed =
                        partition_obligations sq ?depth
                          obligations
                      in
                      if
                        List.exists has_logic_variable
                          obligations
                      then Result.error Apply_logic_variable
                      else if has_logic_variable result then
                        Result.error Apply_logic_variable
                      else begin
                        List.iter term_witness witnessed ;
                        (* Obligation subgoals own the binds from
                           before [recursive_metaterm_case]:
                           focusing one restores them, rolling back
                           any bindings the case analysis performed
                           (as do [Prover]'s subgoal closures). The
                           mainline owns the state from after. *)
                        let schem_ob =
                          !Term.schematic_instantiations
                        in
                        let bs_ob = Term.get_bind_state () in
                        let subgoal_of_goal g =
                          { sq with goal = g }
                        in
                        let ob_cores =
                          List.map subgoal_of_goal remaining
                        in
                        let mainline =
                          match
                            recursive_metaterm_case
                              ~used:sq.vars ~sr:!sr result
                          with
                          | None -> Result.ok []
                          | Some c ->
                              let core =
                                { sq with goal = sq.goal }
                              in
                              let core =
                                List.fold_left
                                  (fun sq v ->
                                    add_if_new_var sq v)
                                  core
                                  c.stateless_new_vars
                              in
                              let core =
                                add_hyps_with_hint core
                                  (Prover.alt_for_subgoal hint
                                     (List.length remaining))
                                  c.stateless_new_hyps
                              in
                              begin match
                                rename_new_vars core
                                  ?alt:(Prover.alt_for_subgoal
                                          hint
                                          (List.length
                                             remaining))
                                  ~base:sq ()
                              with
                              | Result.Error e ->
                                  Result.error (Apply_rename e)
                              | Result.Ok core ->
                                  Result.ok [core]
                            end
                        in
                        begin match mainline with
                        | Result.Error _ as e -> e
                        | Result.Ok mainline ->
                            let schem_main =
                              !Term.schematic_instantiations
                            in
                            let bs_main = Term.get_bind_state () in
                            build_subgoals_full
                              ~mainline:(List.length mainline)
                              sq
                              ((List.map
                                  (fun core ->
                                    (core, bs_ob, schem_ob))
                                  ob_cores)
                               @ (List.map
                                    (fun core ->
                                      (core, bs_main, schem_main))
                                    mainline))
                            |> Result.ok
                        end
                      end)
            end
          end
      end

(* Backchain *)

type backchain_error =
  | Backchain_stmt of stmt_error
  | Backchain_unknown_with_var of id
  | Backchain_type_error of string
  | Backchain_logic_variable
  | Backchain_tactic_failure of string

let type_backchain_withs sq stmt ws =
  let bindings = toplevel_bindings stmt in
  let nctx =
    List.map term_to_pair (metaterm_support sq.goal)
  in
  List.fold_left
    (fun acc (id, t) ->
      match acc with
      | Result.Error _ as e -> e
      | Result.Ok typed -> begin
          match List.assoc_opt id bindings with
          | None ->
              Result.error (Backchain_unknown_with_var id)
          | Some ty -> begin
              try
                let t =
                  type_uterm ~expected_ty:ty ~sr:!sr
                    ~sign:!sign ~ctx:(nctx @ sq.vars) t
                in
                Result.ok (typed @ [(id, t)])
              with
              | TypeInferenceFailure (exp, act, _) ->
                  Result.error
                    (Backchain_type_error
                       (Printf.sprintf "expected %s but got %s"
                          (ty_to_string exp)
                          (ty_to_string act)))
              | Failure msg ->
                  Result.error (Backchain_type_error msg)
            end
        end)
    (Result.ok []) ws

let backchain sq ?depth ?(term_witness = ignore) h ws
    : (sequent list, backchain_error) result =
  match get_stmt_clearly sq h with
  | Result.Error e -> Result.error (Backchain_stmt e)
  | Result.Ok (sq, stmt) -> begin
      match type_backchain_withs sq stmt ws with
      | Result.Error _ as e -> e
      | Result.Ok ws ->
          map_tactic_failure
            (fun msg -> Backchain_tactic_failure msg)
            (fun () ->
              let obligations =
                Tactics.backchain_with ~sr:!sr stmt ws sq.goal
              in
              let remaining, witnessed =
                partition_obligations sq ?depth obligations
              in
              if List.exists has_logic_variable obligations then
                Result.error Backchain_logic_variable
              else begin
                List.iter term_witness witnessed ;
                let schem = !Term.schematic_instantiations in
                let bs = Term.get_bind_state () in
                build_subgoals sq schem bs
                  (List.map (fun g -> { sq with goal = g })
                     remaining)
                |> Result.ok
              end)
    end

(* Case analysis *)

type case_error =
  | Case_stmt of stmt_error
  | Case_undefined_atom
  | Case_rename of rename_hint_error
  | Case_tactic_failure of string

(* Raw case split: resolve (and possibly delete) the
   statement, then run [Tactics.case], returning the updated
   sequent alongside the raw cases. Used by [case] and by
   compute, which manages naming and bind states itself. *)
let case_raw sq h
    : ((sequent * Tactics.case list), case_error) result =
  (* NB: support is computed before resolving (and possibly
     deleting) the cased statement, mirroring [Prover]. *)
  let global_support =
    List.flatten_map metaterm_support
      (List.map (fun h -> h.term) sq.hyps)
    @ metaterm_support sq.goal
  in
  match get_stmt_clearly sq h with
  | Result.Error e -> Result.error (Case_stmt e)
  | Result.Ok (sq, term) ->
      let defs =
        try Result.ok (Prover.def_unfold term)
        with Failure msg ->
          if msg = "Cannot perform case-analysis on undefined atom"
          then Result.error Case_undefined_atom
          else Result.error (Case_tactic_failure msg)
      in
      begin match defs with
      | Result.Error _ as e -> e
      | Result.Ok (mutual, defs) ->
          let state = Term.get_scoped_bind_state () in
          try
            Result.ok
              ( sq,
                Tactics.case ~used:sq.vars ~sr:!sr
                  ~clauses:!Prover.clauses ~mutual ~defs
                  ~global_support term )
          with e -> begin
            Term.set_scoped_bind_state state ;
            match tactic_failure_message e with
            | Some msg -> Result.error (Case_tactic_failure msg)
            | None -> raise e
          end
      end

let case sq ?hint h : (sequent list, case_error) result =
  match case_raw sq h with
  | Result.Error _ as e -> e
  | Result.Ok (sq, cases) -> begin
      let rec build i acc = function
        | [] -> Result.ok (List.rev acc)
        | (c : Tactics.case) :: rest ->
            let core =
              List.fold_left
                (fun sq v -> add_if_new_var sq v)
                sq c.new_vars
            in
            let core =
              add_hyps_with_hint core
                (Prover.alt_for_subgoal hint i)
                c.new_hyps
            in
            begin match
              rename_new_vars core
                ?alt:(Prover.alt_for_subgoal hint i)
                ~base:sq ()
            with
            | Result.Error e ->
                Result.error (Case_rename e)
            | Result.Ok core ->
                (* Install the case binds for the
                   dereference-sensitive update below,
                   mirroring [Prover]. *)
                Term.set_bind_state c.bind_state ;
                let core = update_self_bound_vars core in
                build (i + 1) ((core, c.bind_state) :: acc)
                  rest
            end
      in
      begin match build 0 [] cases with
      | Result.Error _ as e -> e
      | Result.Ok cores ->
          let schem = !Term.schematic_instantiations in
          let named =
            name_subgoals sq (List.map fst cores)
          in
          let bss = List.map snd cores in
          List.mapi
            (fun i core ->
              if i = 0 then
                { core with active = true ; activate = noop }
              else
                let bs = List.nth bss i in
                { core with
                  active = false ;
                  activate =
                    (fun () ->
                      Term.set_bind_state bs ;
                      Term.schematic_instantiations := schem) })
            named
          |> Result.ok
          |> fun r ->
          begin match cores with
          | [] -> r
          | (_, first_bs) :: _ ->
              Term.set_bind_state first_bs ;
              Term.schematic_instantiations := schem ;
              r
          end
      end
    end

(* Assert / monotone share [delay_mainline]: either the
   detour is searched away (one subgoal) or it is stacked
   behind the mainline (two subgoals, detour first). *)

(* [delay_mainline] either discharges the detour immediately
   ([Solved]: an in-place hypothesis addition like other
   single-result tactics, with no normalization) or stacks
   the detour in front of the mainline ([Delayed]:
   branching, normalized on focus). *)

type delayed =
  | Solved of sequent
  | Delayed of sequent list

let delay_mainline sq ?hint ?depth new_hyp detour_goal
    : (delayed, rename_hint_error) result =
  if depth <> Some 0 && search_goal sq ?depth detour_goal then
    Result.ok
      (Solved
         (keep_active sq
            (add_hyp_with_hint sq
               (Prover.alt_for_subgoal hint 0) new_hyp)))
  else
    let mainline_core =
      add_hyps_with_hint sq
        (Prover.alt_for_subgoal hint 1) [new_hyp]
    in
    begin match
      rename_new_vars mainline_core
        ?alt:(Prover.alt_for_subgoal hint 1) ~base:sq ()
    with
    | Result.Error _ as e -> e
    | Result.Ok mainline_core ->
        let idx = sq.next_subgoal_id in
        let detour_name =
          if sq.name = "" then string_of_int idx
          else sq.name ^ "." ^ string_of_int idx
        in
        let detour =
          { { sq with goal = detour_goal } with
            name = detour_name ; next_subgoal_id = 1 }
        in
        let mainline =
          { mainline_core with next_subgoal_id = idx + 1 }
        in
        let schem = !Term.schematic_instantiations in
        let bs = Term.get_bind_state () in
        Result.ok
          (Delayed
             [{ detour with active = true ; activate = noop } ;
              { mainline with
                active = false ;
                activate =
                  (fun () ->
                    Term.set_bind_state bs ;
                    Term.schematic_instantiations := schem) }])
    end

type assert_error =
  | Assert_type_error of string
  | Assert_rename of rename_hint_error

let assert_hyp sq ?hint ?depth term
    : (delayed, assert_error) result =
  let typed =
    try
      Result.ok
        (type_umetaterm ~sr:!sr ~sign:!sign ~ctx:sq.vars term)
    with
    | TypeInferenceFailure (exp, act, _) ->
        Result.error
          (Assert_type_error
             (Printf.sprintf "expected %s but got %s"
                (ty_to_string exp) (ty_to_string act)))
    | Failure msg -> Result.error (Assert_type_error msg)
  in
  match typed with
  | Result.Error _ as e -> e
  | Result.Ok t ->
      delay_mainline sq ?hint ?depth t t
      |> Result.map_error (fun e -> Assert_rename e)

type monotone_error =
  | Monotone_stmt of stmt_error
  | Monotone_not_object
  | Monotone_type_error of string
  | Monotone_rename of rename_hint_error
  | Monotone_tactic_failure of string

let monotone sq ?hint h t
    : (delayed, monotone_error) result =
  match get_stmt_clearly sq h with
  | Result.Error e -> Result.error (Monotone_stmt e)
  | Result.Ok (sq, ht) -> begin
      match ht with
      | Obj (obj, r) ->
          let ntids = metaterm_nominal_tids ht in
          let ctx =
            sq.vars
            @ List.map
                (fun (id, ty) -> (id, nominal_var id ty))
                ntids
          in
          let typed =
            try
              Result.ok
                (type_uterm ~expected_ty:olistty ~sr:!sr
                   ~sign:!sign ~ctx t)
            with
            | TypeInferenceFailure (exp, act, _) ->
                Result.error
                  (Monotone_type_error
                     (Printf.sprintf "expected %s but got %s"
                        (ty_to_string exp) (ty_to_string act)))
            | Failure msg ->
                Result.error (Monotone_type_error msg)
          in
          begin match typed with
          | Result.Error _ as e -> e
          | Result.Ok t ->
              map_tactic_failure
                (fun msg -> Monotone_tactic_failure msg)
                (fun () ->
                  let new_obj =
                    { obj with context = Context.normalize [t] }
                  in
                  delay_mainline sq ?hint
                    (Obj (new_obj, r))
                    (Binding
                       ( Forall,
                         [("X", oty)],
                         Arrow
                           ( member (Term.const "X" oty)
                               (Context.context_to_term
                                  obj.context),
                             member (Term.const "X" oty) t ) ))
                  |> Result.map_error (fun e ->
                      Monotone_rename e))
        end
      | _ -> Result.error Monotone_not_object
    end

(* Unfold *)

type unfold_error =
  | Unfold_tactic_failure of string

let unfold sq clause_sel sol_sel
    : (sequent list, unfold_error) result =
  map_tactic_failure
    (fun msg -> Unfold_tactic_failure msg)
    (fun () ->
      let mdefs = Prover.def_unfold sq.goal in
      let goals =
        Tactics.unfold ~sr:!sr ~used:sq.vars ~mdefs clause_sel
          sol_sel sq.goal
        |> List.flatten_map and_to_list
      in
      let schem = !Term.schematic_instantiations in
      let bs = Term.get_bind_state () in
      build_subgoals sq schem bs
        (List.map (fun g -> { sq with goal = g }) goals)
      |> Result.ok)

(* Skip (infallible, closes the goal). The [skip_seen] flag
   lives in [proof_state]; the scheduler sets it when
   installing this result. *)
let skip _sq = []

let theorem sq thm = keep_active sq { sq with goal = thm }

(* Saturate: fchain-style forward reasoning. Like the other
   branching tactics, the result is a subgoal list in driver
   order, except Or-splits in [release] are expanded eagerly
   (depth-first, as if focused immediately) since subgoals
   here are plain values without continuations. A branch that
   derives [False] contributes nothing, closing its subgoal. *)

exception SaturateSuccess

let is_ground f = metaterm_vars_alist Logic f = []

type saturate_error =
  | Unknown_saturate_lemma of id
  | Saturate_rename of rename_hint_error
  | Saturate_tactic_failure of string

type saturate_case = {
  sc_binds : Term.bind_state ;
  sc_schem : Term.tysub ;
  sc_vars : (id * term) list ;
  sc_hyps : metaterm list ;
  sc_ts : int ;
  sc_index : int ;
}

type focus_outcome =
  | NoRelease
  | Released of saturate_case list

let saturate sq ?hint ?depth lemmas
    : (sequent list, saturate_error) result =
  let focus_lemmas =
    List.fold_left
      (fun acc name ->
        match acc with
        | Result.Error _ as e -> e
        | Result.Ok l -> begin
            match get_hyp_or_lemma sq name with
            | Result.Error _ ->
                (* Only [Unknown_stmt] is reachable here:
                   [tys] default to fresh variables. *)
                Result.error (Unknown_saturate_lemma name)
            | Result.Ok form -> Result.ok (l @ [form])
          end)
      (Result.ok []) lemmas
  in
  match focus_lemmas with
  | Result.Error _ as e -> e
  | Result.Ok focus_lemmas ->
      map_tactic_failure
        (fun msg -> Saturate_tactic_failure msg)
        (fun () ->
          let depth0 =
            match depth with
            | None -> List.length lemmas
            | Some depth -> depth
          in
          (* Saturate does not handle nabla, so everything is
             raised over the global support, computed once. *)
          let global_support =
            (List.flatten_map
               (fun (h : hyp) -> metaterm_support h.term)
               sq.hyps @
             metaterm_support sq.goal)
            |> List.unique ~cmp:eq
          in
          let next_index =
            let index = ref 0 in
            fun () ->
              let i = !index in
              incr index ;
              i
          in
          let rec loop sq depth ts =
            let sq = clear_duplicates sq in
            if depth <= 0 then
              let bs = Term.get_bind_state () in
              let schem = !Term.schematic_instantiations in
              Ok [(sq, bs, schem)]
            else
              let foci =
                List.map (normalize ~used:sq.vars) focus_lemmas
              in
              try_foci sq foci depth ts
          and try_foci sq foci depth ts =
            match foci with
            | [] ->
                let bs = Term.get_bind_state () in
                let schem = !Term.schematic_instantiations in
                Ok [(sq, bs, schem)]
            | focus :: rest ->
                let state = Term.get_scoped_bind_state () in
                begin match multifocus sq ~ts [] [focus] with
                | NoRelease ->
                    Term.set_scoped_bind_state state ;
                    try_foci sq rest depth ts
                | Released cases ->
                    expand_cases sq cases depth
                end
          and expand_cases sq cases depth =
            match cases with
            | [] -> Ok []
            | c :: rest ->
                Term.set_bind_state c.sc_binds ;
                Term.schematic_instantiations := c.sc_schem ;
                let alt = Prover.alt_for_subgoal hint c.sc_index in
                let core =
                  List.fold_left
                    (fun sq v -> add_if_new_var sq v)
                    sq c.sc_vars
                in
                let core = add_hyps_with_hint core alt c.sc_hyps in
                begin match rename_new_vars core ?alt ~base:sq () with
                | Result.Error e ->
                    Result.error (Saturate_rename e)
                | Result.Ok core ->
                    let core = update_self_bound_vars core in
                    begin match loop core (depth - 1) c.sc_ts with
                    | Result.Error _ as e -> e
                    | Result.Ok done1 ->
                        begin match expand_cases sq rest depth with
                        | Result.Error _ as e -> e
                        | Result.Ok donerest ->
                            Result.ok (done1 @ donerest)
                        end
                    end
                end
          and multifocus sq ~ts:ts dead live =
            match live with
            | [] ->
                let to_release =
                  List.rev_filter_map begin fun form ->
                    if not @@ is_ground form then None else
                    match
                      purepos sq ~ts
                        ~succ:(fun _ts -> raise SaturateSuccess)
                        form
                    with
                    | _ -> Some form
                    | exception SaturateSuccess -> None
                  end dead in
                let num_released = List.length to_release in
                if num_released = 0 then NoRelease
                else
                  Released
                    (release sq ~ts ~nvs:[] ~nhs:[] to_release)
            | form :: live -> begin
                match form with
                | True -> multifocus sq ~ts:ts dead live
                | Arrow (f1, f2) ->
                    let cases = ref [] in
                    let add_proof _ts =
                      let f1 =
                        Metaterm.map_terms Term.deep_copy f1
                      in
                      let f2 =
                        Metaterm.map_terms Term.deep_copy f2
                      in
                      if is_ground f1 then
                        cases := (f1, f2) :: !cases
                    in
                    purepos sq ~ts ~succ:add_proof f1 ;
                    let live =
                      List.rev_map (fun (_, f2) -> f2) !cases
                      @ live
                    in
                    multifocus sq ~ts:ts dead live
                | Binding (Forall, vs, form) ->
                    let ts = ts + 1 in
                    let alist =
                      fresh_nameless_alist ~sr:!sr
                        ~support:global_support ~tag:Logic ~ts vs
                    in
                    let form =
                      replace_metaterm_vars alist form
                    in
                    multifocus sq ~ts:ts dead (form :: live)
                | (False | Eq _ | Binding (Exists, _, _)
                  | And _ | Or _ | Pred _) ->
                    multifocus sq ~ts:ts (form :: dead) live
                | _ ->
                    multifocus sq ~ts:ts dead live
              end
          and purepos sq ~ts ~succ form =
            match form with
            | True -> succ ts
            | False -> ()
            | Or (f1, f2) ->
                purepos sq ~ts ~succ f1 ;
                purepos sq ~ts ~succ f2
            | And (f1, f2) ->
                purepos sq ~ts f1
                  ~succ:(fun ts -> purepos sq ~ts ~succ f2)
            | Binding (Exists, vs, form) ->
                let alist =
                  fresh_nameless_alist ~sr:!sr
                    ~support:global_support ~tag:Logic ~ts vs
                in
                let form = replace_metaterm_vars alist form in
                purepos sq ~ts ~succ form
            | Eq (t1, t2) ->
                unwind_state begin fun () ->
                  if Unify.try_right_unify t1 t2 then succ ts
                end ()
            | Pred (_, cr) ->
                List.iter ~guard:unwind_state begin fun h ->
                  match (h : hyp).term with
                  | Pred (_, hr) ->
                      if satisfies hr cr then
                        all_meta_right_permute_unify
                          ~sc:(fun _ -> succ ts) form h.term
                  | _ -> ()
                end
                  (List.unique
                     ~cmp:(fun (h1 : hyp) (h2 : hyp) ->
                       h1.term = h2.term)
                     sq.hyps)
            | Arrow _ | Binding _ | Obj _ -> ()
          and release sq ~ts ~nvs ~nhs forms =
            match forms with
            | [] ->
                let nvs = List.rev nvs in
                let nhs = List.rev nhs in
                [{ sc_binds = Term.get_bind_state () ;
                   sc_schem = !Term.schematic_instantiations ;
                   sc_vars = nvs ;
                   sc_hyps = nhs ;
                   sc_ts = ts ;
                   sc_index = next_index () }]
            | form :: forms -> begin
                match form with
                | True -> release sq ~ts ~nvs ~nhs forms
                | False -> []
                | Or (f1, f2) ->
                    let state = Term.get_scoped_bind_state () in
                    let cs1 =
                      release sq ~ts ~nvs ~nhs (f1 :: forms)
                    in
                    Term.set_scoped_bind_state state ;
                    let cs2 =
                      release sq ~ts ~nvs ~nhs (f2 :: forms)
                    in
                    cs1 @ cs2
                | And (f1, f2) ->
                    release sq ~ts ~nvs ~nhs (f1 :: f2 :: forms)
                | Binding (Exists, vs, form) ->
                    let (alist, vars) =
                      fresh_raised_alist ~sr:!sr
                        ~support:global_support
                        ~used:(nvs @ sq.vars) ~tag:Eigen vs
                    in
                    let nvs =
                      List.rev_map term_to_pair vars @ nvs
                    in
                    let form =
                      replace_metaterm_vars alist form
                    in
                    release sq ~ts ~nvs ~nhs (form :: forms)
                | Eq (t1, t2) -> begin
                    match
                      Unify.try_left_unify_cpairs
                        ~used:(nvs @ sq.vars) t1 t2
                    with
                    | Some cpairs ->
                        let nhs =
                          List.map
                            (fun (t1, t2) -> Eq (t1, t2))
                            cpairs @ nhs
                        in
                        release sq ~ts ~nvs ~nhs forms
                    | None -> []
                  end
                | _ ->
                    let nhs =
                      if List.mem form nhs then nhs
                      else form :: nhs
                    in
                    release sq ~ts ~nvs ~nhs forms
              end
          in
          begin match loop sq depth0 0 with
          | Result.Error _ as e -> e
          | Result.Ok triples ->
              Result.ok (build_subgoals_full sq triples)
          end)

(* Proof state: explicit version of [Prover.subgoals],
   [Prover.bullet_stack] and [Prover.subgoal_focused].
   Branching tactics above produce subgoal lists; the
   scheduler installs them here. *)

type bullet_frame = {
  bullet : string ;
  siblings : sequent list ;
}

type proof_state = {
  focused : sequent option ;
  pending : sequent list ;
  bullets : bullet_frame list ;
  skip_seen : bool ;
}

type bullet_error =
  | Bullet_already_active of string
  | Wrong_bullet of { expected : string ; got : string }
  | Unfocused_no_bullets
  | No_focused_subgoal of string

let start_proof sq =
  { focused = Some sq ; pending = [] ; bullets = [] ;
    skip_seen = false }

(* Install tactic results: the first subgoal stays focused,
   the rest wait behind it (driver order preserved). *)
let push_subgoals st subs =
  match subs with
  | [] -> { st with focused = None }
  | first :: rest ->
      { st with
        focused = Some (activate_sequent first) ;
        pending = rest @ st.pending }

let rec next_subgoal st =
  match st.pending with
  | [] -> begin
      match st.bullets with
      | { siblings = [] ; _ } :: rest ->
          next_subgoal { st with bullets = rest }
      | _ :: _ -> { st with focused = None }
      | [] -> { st with focused = None }
    end
  | sq :: rest ->
      { st with
        focused = Some (activate_sequent sq) ;
        pending = rest }

let is_completed st =
  Option.is_none st.focused
  && st.pending = []
  && st.bullets = []

let bullet st b : (proof_state, bullet_error) result =
  match st.focused with
  | Some _ ->
      if List.exists (fun f -> f.bullet = b) st.bullets then
        Result.error (Bullet_already_active b)
      else
        Result.ok
          { st with
            bullets = [{ bullet = b ; siblings = st.pending }] ;
            pending = [] }
  | None -> begin
      match st.bullets with
      | [] -> Result.error Unfocused_no_bullets
      | { bullet = expected ; siblings = next :: rest }
        :: stack_rest ->
          if b <> expected then
            Result.error (Wrong_bullet { expected ; got = b })
          else
            Result.ok
              { st with
                focused = Some (activate_sequent next) ;
                pending = [] ;
                bullets =
                  { bullet = expected ; siblings = rest }
                  :: stack_rest }
      | { siblings = [] ; _ } :: _ ->
          Result.error Unfocused_no_bullets
    end
