(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(* Copyright (C) 2013-2022 Inria (Institut National de Recherche            *)
(*                         en Informatique et en Automatique)               *)
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
open Format
open Tactics
open Checks
open Abella_types
open Extensions
open Unifyty

module H = Hashtbl

let lemmas : (string, string list * metaterm) H.t = State.table ()

type subgoal = unit -> unit
let subgoals : subgoal list ref = State.rref []

let skip_seen : bool ref = State.rref false
let start_proof () = skip_seen := false

type hyp = {
  id : id ;
  term : metaterm ;
  abbrev : string option ;
}

type sequent = {
  mutable vars : (id * term) list ;
  mutable hyps : hyp list ;
  mutable goal : metaterm ;
  mutable count : int ;
  mutable name : string ;
  mutable next_subgoal_id : int ;
}

(* The vars = sq.vars is superfluous, but forces the copy *)
let cp_sequent sq = {sq with vars = sq.vars}
let assign_sequent sq1 sq2 =
  sq1.vars <- sq2.vars ;
  sq1.hyps <- sq2.hyps ;
  sq1.goal <- sq2.goal ;
  sq1.count <- sq2.count ;
  sq1.name <- sq2.name ;
  sq1.next_subgoal_id <- sq2.next_subgoal_id

let sequent =
  State.make ~copy:cp_sequent ~assign:assign_sequent {
    vars = [] ;
    hyps = [] ;
    goal = termobj (const "placeholder" propty) ;
    count = 0 ;
    name = "" ;
    next_subgoal_id = 1 ;
  }

let add_global_types tys knd =
  sign := add_types !sign tys knd

let locally_add_global_consts cs =
  let local_sr = List.fold_left Subordination.update !sr (List.map snd cs)
  and local_sign = add_consts !sign cs
  in (local_sr, local_sign)

let commit_global_consts local_sr local_sign =
  sr := local_sr ;
  sign := local_sign

let add_global_consts cs =
  sr := List.fold_left Subordination.update !sr (List.map snd cs) ;
  sign := add_consts !sign cs

let close_types sign clauses atys =
  List.iter (kind_check sign) (List.map tybase atys);
  let tys = List.map tybase atys in
  begin match List.intersect [oty; olistty; propty] tys with
  | [] -> ()
  | xs -> failwithf "Cannot close %s"
            (String.concat ", " (List.map ty_to_string xs))
  end ;
  sr := Subordination.close !sr atys;
  List.iter (Typing.term_ensure_subordination !sr) (List.map snd clauses)

let add_subgoals ?(mainline) new_subgoals =
  let extend_name i =
    if sequent.name = "" then
      sequent.name <- string_of_int i
    else
      sequent.name <- sequent.name ^ "." ^ (string_of_int i)
  in
  let rec annotate i gs =
    match gs with
    | [] -> []
    | g::rest ->
        (fun () -> g (); extend_name i; sequent.next_subgoal_id <- 1) ::
        annotate (i+1) rest
  in
  let n = List.length new_subgoals in
  let annotated_subgoals =
    match mainline with
    | None ->
        if n > 1 then
          annotate sequent.next_subgoal_id new_subgoals
        else
          new_subgoals
    | Some mainline ->
        let new_mainline () =
          mainline () ;
          sequent.next_subgoal_id <- sequent.next_subgoal_id + n
        in
        annotate sequent.next_subgoal_id new_subgoals @ [new_mainline]
  in
  subgoals := annotated_subgoals @ !subgoals

let copy_sequent () = cp_sequent sequent
let set_sequent other = assign_sequent sequent other

let fresh_hyp_name base =
  if base = "" then begin
    sequent.count <- sequent.count + 1 ;
    "H" ^ (string_of_int sequent.count)
  end else
    fresh_name base (List.map (fun h -> (h.id, ())) sequent.hyps)

(* let normalize mt = *)
(*   let before = metaterm_to_string mt in *)
(*   Printf.fprintf stderr "normalizing\n%s\n%!" before ; *)
(*   let mt = normalize mt in *)
(*   let after = metaterm_to_string mt in *)
(*   Printf.fprintf stderr "normalized form\n%s\n%!" after ; *)
(*   mt *)

let normalize_sequent () =
  (* Printf.fprintf stderr "Normalizing Sequent %s\n%!" sequent.name ; *)
  sequent.goal <- normalize sequent.goal ;
  sequent.hyps <-
    sequent.hyps |> List.map (fun h -> { h with term = normalize h.term })

(* Clauses *)

let clauses : clause list ref = State.rref []

let add_clauses new_clauses =
  clauses := !clauses @ new_clauses

let defs_table : defs_table = State.table ()

let built_ins_done = ref false

let add_defs typarams preds flavor clauses =
  List.iter begin fun (id, _) ->
    if H.mem defs_table id then
      failwithf "Predicate %s has already been defined" id ;
  end preds ;
  (* List.iter begin fun (head, body) -> *)
  (*   Format.eprintf "%a := %a@." format_metaterm head format_metaterm body *)
  (* end defs ; *)
  let mutual = List.fold_left begin fun mutual (id, ty) ->
      Itab.add id ty mutual
    end Itab.empty preds in
  let def = {flavor ; typarams ; mutual ; clauses} in
  Checks.check_def ~def ;
  List.iter (fun (id, _) -> H.add defs_table id def) preds

let lookup_poly_const k =
  try let Poly (typarams, ty) = List.assoc k (snd !sign) in (typarams, ty) with
  | Not_found -> failwithf "Unknown constant: %S" k


let register_definition = function
  | Define (flav, idtys, udefs) ->
      let typarams = List.unique (idtys |> List.map snd |> get_typarams) in
      check_typarams typarams (List.map snd idtys);
      let ids = List.map fst idtys in
      check_noredef ids;
      let (basics, consts) = !sign in
      (* Note that in order to type check the definitions, the types
         of predicates being defined are fixed to their most generic
         form by fixing the type variables in them to generic ones *)
      let consts = List.map (fun (id, ty) -> (id, Poly ([], ty))) idtys @ consts in
      let clauses = type_udefs ~sr:!sr ~sign:(basics, consts) udefs |>
                    List.map (fun (head, body) -> {head ; body}) in
      ensure_no_schm_clauses typarams clauses;
      let (basics, consts) = !sign in
      let consts = List.map (fun (id, ty) -> (id, Poly (typarams, ty))) idtys @ consts in
      sign := (basics, consts) ;
      add_defs typarams idtys flav clauses ;
      CDefine (flav, typarams, idtys, clauses)
  | _ -> [%bug] "Not a definition!"

let k_member = "member"
let member_def =
  let ty_a = tybase @@ Tygenvar "A" in
  let ty_list_a = tybase @@ Tycons ("list", [ty_a]) in
  let ty_member = tyarrow [ty_a ; ty_list_a] propty in
  let const k = UCon (ghost_pos, k, fresh_tyvar ()) in
  let rec app f ts =
    match ts with
    | [] -> f
    | t :: ts -> app (UApp (ghost_pos, f, t)) ts
  in
  let clause_nil : udef_clause =
    let head = app (const "member") [const "A" ;
                                     app (const k_cons) [const "A" ;
                                                         const "L"]] in
    (UPred (head, Irrelevant), UTrue) in
  let clause_cons : udef_clause =
    let head = app (const "member") [const "A" ;
                                     app (const k_cons) [const "B" ;
                                                         const "L"]] in
    let body = app (const "member") [const "A" ; const "L"] in
    (UPred (head, Irrelevant), UPred (body, Irrelevant)) in
  Define (Inductive, ["member", ty_member], [clause_nil ; clause_cons])
  |> register_definition

let () = built_ins_done := true

let term_spine t =
  match term_head t with
  | Some (_, spine) -> spine
  | None -> assert false

let clause_head_name cl =
  match cl.head with
  | Binding (Nabla, _, Pred (p, _)) | Pred (p, _) ->
      term_head_name p
  | _ -> [%bug] "Clause head name for invalid clause: %s" (metaterm_to_string cl.head)

(* let rec app_ty tymap = function
 *   | Ty (args, res) ->
 *       let args = List.map (app_ty tymap) args in
 *       let res = try Itab.find res tymap with Not_found -> tybase res in
 *       tyarrow args res *)

(* let instantiate_clauses_aux =
 *   let fn (pn, ty_acts) def =
 *     let Ty (ty_exps, _) = Itab.find pn def.mutual in
 *     let ty_fresh = List.fold_left begin fun fresh_sub tyvar ->
 *         let tv = Term.fresh_tyvar () in
 *         Itab.add tyvar tv fresh_sub
 *       end Itab.empty def.typarams in
 *     let ty_exps = List.map (app_ty ty_fresh) ty_exps in
 *     let eqns = List.map2 begin fun ty_exp ty_act ->
 *         (ty_exp, ty_act, (ghost, CArg))
 *       end ty_exps ty_acts in
 *     let tysol = unify_constraints eqns in
 *     let tymap = List.fold_left begin fun tymap tyv ->
 *         try begin
 *           let Ty (_, tyf) = Itab.find tyv ty_fresh in
 *           Itab.add tyv (List.assoc tyf tysol) tymap
 *         end with Not_found -> tymap
 *       end Itab.empty def.typarams in
 *     (\* Itab.iter begin fun v ty -> *\)
 *     (\*   Format.eprintf "instantiating: %s <- %s@." v (ty_to_string ty) *\)
 *     (\* end tymap ; *\)
 *     List.map begin fun cl ->
 *       if clause_head_name cl = pn then
 *         {head = map_on_tys (app_ty tymap) cl.head ;
 *          body = map_on_tys (app_ty tymap) cl.body}
 *       else cl
 *     end def.clauses
 *   in
 *   memoize fn *)

(* let instantiate_clauses pn def args =
 *   let ty_acts = List.map (tc []) args in
 *   instantiate_clauses_aux (pn, ty_acts) def *)

let instantiate_pred_types tysub (tbl: ty Itab.t) : ty Itab.t =
  let res = ref Itab.empty in
  Itab.iter begin fun id ty ->
    let ty' = apply_sub_ty tysub ty in
    res := Itab.add id ty' !res
  end tbl;
  !res

let instantiate_clause tysub cl =
  let head = map_on_tys (apply_sub_ty tysub) cl.head in
  let body = map_on_tys (apply_sub_ty tysub) cl.body in
  {head = head; body = body}

let instantiate_clauses p def =
  let pn = term_head_name p in
  let pty = term_head_ty p in
  let clauses = def.clauses in
  let tysub = List.map (fun id -> (id, Term.fresh_tyvar ())) def.typarams in
  let mutual = instantiate_pred_types tysub def.mutual in
  let dpty = Itab.find pn mutual in
  unify_constraints [(pty, dpty, def_cinfo)];
  assert (ty_tyvars dpty = []);
  let clauses = List.map (instantiate_clause tysub) clauses in
  (mutual, clauses)

let def_unfold term =
  match term with
  | Pred(p, _) ->
      let pn = term_head_name p in
      if H.mem defs_table pn then begin
        let def = H.find defs_table pn in
        let (mutual, clauses) = instantiate_clauses p def in
        List.iter begin fun cl ->
          metaterm_ensure_subordination !sr cl.head ;
          metaterm_ensure_subordination !sr cl.body
        end clauses;
        (mutual,clauses)
      end else
        failwith "Cannot perform case-analysis on undefined atom"
  | _ -> (Itab.empty, [])


(* Pretty print *)

let sequent_var_to_string (x, _xt) =
  x (* ^ "(=" ^ term_to_string xt ^ ")" *)

let show_instantiations = State.rref false

let separate_strings xs =
  let __max_len = 30 in
  let result = ref [] in
  let emit xs = result := String.concat "," (List.rev xs) :: !result in
  let rec spin nxs pos = function
    | [] -> emit nxs
    | x :: xs ->
        if pos + String.length x + 1 < __max_len then
          spin (x :: nxs) (pos + String.length x + 1) xs
        else begin
          emit nxs ;
          spin [x] (String.length x) xs
        end
  in
  spin [] 0 xs ;
  List.rev !result

let format_typed_vars ff (ty, xs) =
  let open Format in
  List.iter begin fun xs ->
    pp_print_string ff "  " ;
    pp_print_string ff xs ;
    pp_print_string ff " : " ;
    pp_open_box ff 0 ; Term.format_ty ff ty ; pp_close_box ff () ;
    pp_print_newline ff () ;
  end (separate_strings xs)

let format_vars ff =
  let open Format in
  let (eigen_vars, inst_vars) =
    List.partition is_uninstantiated sequent.vars in
  if eigen_vars <> [] then begin
    pp_print_string ff "Variables: " ;
    if !show_types then begin
      pp_print_newline ff () ;
      eigen_vars
      |> List.map (fun (x, xtm) -> (Term.tc [] xtm, x))
      |> List.sort (fun (ty1, _) (ty2, _) -> compare ty1 ty2)
      |> List.collate_assoc
      |> List.iter (format_typed_vars ff) ;
    end else begin
      pp_open_hovbox ff 0 ; begin
        pp_print_string ff (sequent_var_to_string (List.hd eigen_vars)) ;
        List.iter begin
          fun v ->
            pp_print_space ff () ;
            pp_print_string ff (sequent_var_to_string v)
        end (List.tl eigen_vars) ;
      end ; pp_close_box ff () ;
      pp_print_newline ff ()
    end
  end ;
  if inst_vars <> [] && !show_instantiations then
    List.iter begin fun (v, vtm) ->
      pp_print_string ff v ;
      pp_print_string ff " <-- " ;
      Term.format_term ff vtm ;
      pp_print_newline ff () ;
    end inst_vars

let format_hyp fmt hyp =
  fprintf fmt "%s : " hyp.id ;
  begin match hyp.abbrev with
  | None -> format_metaterm fmt hyp.term
  | Some s -> fprintf fmt "%s" s
  end;
  pp_force_newline fmt ()

let format_hyps fmt =
  let (am, hyps) = List.fold_left begin fun (am, hs) h ->
      match h.abbrev with
      | None -> (am, h :: hs)
      | Some ab ->
          let am = match Itab.find ab am with
            | hs -> Itab.add ab (h.id :: hs) am
            | exception Not_found -> Itab.add ab [h.id] am
          in
          (am, hs)
    end (Itab.empty, []) sequent.hyps
  in
  Itab.iter begin fun ab hs ->
    fprintf fmt "%s : %s@\n" (String.concat "," (List.rev hs)) ab
  end am ;
  List.iter (format_hyp fmt) (List.rev hyps)

let format_count_subgoals fmt n =
  match n with
  | 0 -> ()
  | 1 -> fprintf fmt "1 other subgoal.@\n@\n"
  | n -> fprintf fmt "%d other subgoals.@\n@\n" n

type subgoal_max = {
  smax_default : int ;
  smax_map : int IntMap.t ;
}
let subgoal_max_init = { smax_default = max_int ;
                         smax_map = IntMap.empty }
let subgoal_max : subgoal_max ref = State.rref subgoal_max_init
let reset_subgoal_max () =
  subgoal_max := subgoal_max_init
let set_subgoal_max_default smax_default =
  let smax = !subgoal_max in
  subgoal_max := { smax with smax_default }
let set_subgoal_max ndps =
  let smax = !subgoal_max in
  let smax_map = List.fold_left begin
      fun smax_map (dp, n) ->
        let n = Option.value ~default:max_int n in
        (* Printf.printf "Max subgoals at depth %d: %d\n%!" dp n ; *)
        IntMap.add dp n smax_map
    end smax.smax_map ndps in
  subgoal_max := { smax with smax_map }

let format_other_subgoals fmt =
  let pristine = State.snapshot () in
  let smax = !subgoal_max in
  let smax_map = ref smax.smax_map in
  let count = ref 0 in
  List.iter begin fun set_state ->
    set_state () ;
    let goal_depth = String.count sequent.name '.' in
    let max_goals =  try IntMap.find goal_depth !smax_map with Not_found -> smax.smax_default in
    (* Printf.printf "Showing %d goals at depth %d\n%!" max_goals goal_depth ; *)
    if max_goals > 0 then begin
      smax_map := IntMap.add goal_depth (max_goals - 1) !smax_map ;
      fprintf fmt "@[<1>Subgoal %s%sis:@\n%a@]@\n@\n"
        sequent.name
        (if sequent.name = "" then "" else " ")
        format_metaterm (normalize sequent.goal)
    end else incr count
  end !subgoals ;
  format_count_subgoals fmt !count ;
  State.reload pristine

let format_sequent_with_goal fmt goal =
  pp_open_vbox fmt 0 ; begin
    format_vars fmt ;
    format_hyps fmt ;
    fprintf fmt "============================@\n " ;
    format_metaterm fmt goal
  end ; pp_close_box fmt ()

let format_sequent fmt =
  format_sequent_with_goal fmt sequent.goal

let format_display fmt =
  pp_open_box fmt 0 ;
  if sequent.name = "" then
    fprintf fmt "@\n"
  else
    fprintf fmt "Subgoal %s:@\n@\n" sequent.name;
  format_sequent fmt ;
  fprintf fmt "@\n@\n" ;
  format_other_subgoals fmt ;
  pp_close_box fmt () ;
  pp_print_flush fmt ()

let display out =
  format_display (formatter_of_out_channel out)

let get_display () =
  let b = Buffer.create 100 in
  format_display (formatter_of_buffer b) ;
  Buffer.contents b

let state_json () : Json.t =
  let vars = List.map begin fun ((v, t) as vt) ->
      `List [ `String v ;
              if is_uninstantiated vt then `Null else
                `String (term_to_string t) ]
    end sequent.vars in
  let hyps = List.map begin fun h ->
      `List [
        `String h.id ;
        `String (metaterm_to_string h.term) ;
      ]
    end sequent.hyps in
  let goal = metaterm_to_string sequent.goal in
  `Assoc [
    "more", `Int (List.length !subgoals) ;
    "goal", `String goal ;
    "hyps", `List hyps ;
    "vars", `List vars ;
    "name", `String sequent.name ;
  ]

(* Proof state manipulation utilities *)

let reset_prover original_state original_sequent () =
  set_bind_state original_state ;
  set_sequent original_sequent ;
  subgoals := []

let full_reset_prover original_state original_sequent
    original_clauses original_defs_table () =
  reset_prover original_state original_sequent () ;
  clauses := original_clauses ;
  H.assign defs_table original_defs_table

(** Update sequent.count based on whether name is of the form
    H<num> *)
let update_hyp_count name =
  if name.[0] <> 'H' then () else
  match int_of_string (String.sub name 1 (String.length name - 1)) with
  | n -> sequent.count <- max sequent.count n
  | exception _ -> ()

let unsafe_add_hyp name term =
  let h = { id = name ; term = term ; abbrev = None } in
  sequent.hyps <- List.append sequent.hyps [h] ;
  h

let add_hyp_ ?name term =
  let name = fresh_hyp_name begin
      match name with
      | None -> ""
      | Some name -> name
    end in
  update_hyp_count name ;
  unsafe_add_hyp name term

let add_hyp ?name term = ignore (add_hyp_ ?name term)

let remove_hyp cm name =
  let removed_h = ref None in
  let hyps = List.filter begin fun h ->
      h.id <> name || begin
        removed_h := Some h ;
        false
      end
    end sequent.hyps in
  sequent.hyps <- hyps ;
  match cm, !removed_h with
  | Clear_extro, Some h ->
      sequent.goal <- Arrow (h.term, sequent.goal)
  | Clear_extro, None ->
      failwithf "Cannot extrude unknown hypothesis %s" name
  | _ -> ()

let replace_hyp name t =
  let rec aux hyplist =
    match hyplist with
    | [] -> []
    | hyp::rest when hyp.id = name -> {hyp with term = t} :: rest
    | hyp::rest -> hyp :: (aux rest)
  in
  sequent.hyps <- aux sequent.hyps

let add_var v =
  sequent.vars <- List.append sequent.vars [v]

let add_if_new_var (name, v) =
  if not (List.mem_assoc name sequent.vars) then
    add_var (name, v)

let add_lemma name tys lemma =
  let ovr = if H.mem lemmas name then `replace else `append in
  H.replace lemmas name (tys, lemma) ;
  ovr

let get_hyp name =
  let hyp = List.find (fun h -> h.id = name) sequent.hyps in
  hyp.term

let is_hyp name =
  List.exists (fun h -> h.id = name) sequent.hyps

let get_generic_lemma name =
  try H.find lemmas name with
  | Not_found ->
      failwithf "Could not find theorem named %S" name

let get_lemma ?(tys:ty list = []) name =
  let (argtys, bod) = H.find lemmas name in
  let tys =
    if (List.length argtys > 0 && List.length tys = 0) then
      List.map (fun _t -> fresh_tyvar ()) argtys
    else if List.length tys <> List.length argtys then
      failwithf "Need to provide mappings for %d types" (List.length argtys)
    else
      tys in
  let tysub = List.map2 (fun id ty -> (id,ty)) argtys tys in
  map_on_tys (apply_sub_ty tysub) bod

let get_hyp_or_lemma ?tys name =
  try get_hyp name with
  | Not_found -> get_lemma ?tys name

let stmt_name = function
  | Keep (h, _) | Remove (h, _) -> h

let get_stmt_clearly h =
  try begin
    match h with
    | Keep (h, tys) ->
        get_hyp_or_lemma ~tys h
    | Remove (h, []) when is_hyp h ->
        let stmt = get_hyp h in
        remove_hyp Clear_delete h ; stmt
    | Remove (h, tys) ->
        get_lemma ~tys h
  end
  with Not_found ->
    failwithf "Could not find hypothesis or lemma %s" (stmt_name h)

let get_arg_clearly = function
  | Keep ("_", _) -> None
  | arg -> Some (get_stmt_clearly arg)

exception End_proof of [`completed of fin | `aborted]

let next_subgoal () =
  match !subgoals with
  | [] ->
      let fin = if !skip_seen then Unfinished else Finished in
      raise (End_proof (`completed fin))
  | set_subgoal::rest ->
      set_subgoal () ;
      subgoals := rest ;
      normalize_sequent ()

(* Show *)

let print_theorem name (tys, thm) fmt =
  Format.fprintf fmt "@[<hv2>Theorem %s%s :@ %a@].@."
    name (gen_to_string tys) format_metaterm thm

let show name fmt =
  print_theorem name (get_generic_lemma name) fmt

(* Object level instantiation *)

let inst ?name h ws =
  let ht = get_stmt_clearly h in
  match ht with
  | Obj _ ->
      let rec aux ws ht = match ws with
        | [] -> add_hyp ?name ht
        | (n, t) :: ws ->
            let ntids = metaterm_nominal_tids ht in
            let nty = try List.assoc n ntids with
              | Not_found -> failwithf "Nominal constant %s not in support" n in
            let ctx = sequent.vars @
                      (List.map (fun (id, ty) -> (id, nominal_var id ty)) ntids)
            in
            let t = type_uterm ~expected_ty:nty ~sr:!sr ~sign:!sign ~ctx t in
            aux ws (object_inst ht n t)
      in
      aux ws ht
  | _ ->
      failwith "Cannot instantiate this hypothesis\n\
              \ Instantiation can only be used on hypotheses of the form {...}"


(* Object level cut *)

let cut ?name h arg =
  let h = get_stmt_clearly h in
  let arg = get_stmt_clearly arg in
  match h, arg with
  | Obj(obj_h, _), Obj(obj_arg, _) ->
      add_hyp ?name (object_cut obj_h obj_arg)
  | _ -> failwith "Cut can only be used on hypotheses of the form {...}"

(* Search *)

let retype t = type_uterm ~sr:!sr ~sign:!sign ~ctx:sequent.vars t

let has_inductive_hyps hyp =
  let rec aux term =
    match term with
    | Binding(Forall, _, body) -> aux body
    | Binding(Nabla, _, body) -> aux body
    | Arrow(Obj(_, Smaller _i), _) -> true
    | Arrow(Pred(_, Smaller _i), _) -> true
    | Arrow(_left, right) -> aux right
    | _ -> false
  in
  aux hyp.term

let remove_inductive_hypotheses hyps =
  List.remove_all has_inductive_hyps hyps

let has_coinductive_result hyp =
  let rec aux term nested =
    match term with
    | Binding(Forall, _, body) -> aux body true
    | Binding(Nabla, _, body) -> aux body true
    | Arrow(_left, right) -> aux right true
    | Pred(_, CoSmaller _) -> nested
    | Pred(_, CoEqual _) -> nested
    | _ -> false
  in
  aux hyp.term false

let remove_coinductive_hypotheses hyps =
  List.remove_all has_coinductive_result hyps

let search_depth = State.rref 5

let search_goal_witness ?depth goal witness =
  let hyps = sequent.hyps
             |> remove_inductive_hypotheses
             |> remove_coinductive_hypotheses
             |> List.map (fun h -> (h.id, h.term))
  in
  let depth = Option.value ~default:!search_depth depth in
  Tactics.search
    ~depth
    ~hyps
    ~clauses:!clauses
    ~def_unfold
    ~sr:!sr
    ~retype
    ~witness
    goal

let search_goal ?depth goal =
  try Option.is_some (search_goal_witness ?depth goal WMagic)
  with Failure _ -> false

let search ?depth ~witness ~handle_witness () =
  let search_result = search_goal_witness ?depth sequent.goal witness in
  match search_result with
  | None -> failwith "Search failed"
  | Some w -> handle_witness w ; next_subgoal ()

(* Search cut *)

let search_cut ?name h =
  match get_stmt_clearly h with
  | Obj(obj, _) ->
      add_hyp ?name (Obj(Tactics.search_cut ~search_goal obj, Irrelevant))
  | _ ->
      failwith "Cut can only be used on hypotheses of the form {... |- ...}"

(* Apply *)

let goal_to_subgoal g =
  let saved_sequent = copy_sequent () in
  let bind_state = Term.get_bind_state () in
  fun () ->
    set_sequent saved_sequent ;
    Term.set_bind_state bind_state ;
    sequent.goal <- g

let ensure_no_logic_variable term =
  let logic_vars = metaterm_vars_alist Logic term in
  if logic_vars <> [] then
    failwithf {|Found logic variable at toplevel.
This usually means that the `search` tactic could not fully solve a goal.
Note: the `search` tactic may have been invoked implicitly by `apply`,
`backchain`, etc. with unknown arguments.|}

let ensure_no_restrictions term =
  let rec aux t nested =
    match t with
    | Binding(Forall, _, body) -> aux body true
    | Binding(Nabla, _, body) -> aux body true
    | Arrow(left, right) -> aux left true; aux right true
    | Obj(_, Smaller _i) | Obj(_, Equal _i)
    | Pred(_, Smaller _i) | Pred(_, Equal _i) ->
        if nested then
          failwithf "Inductive restrictions must not occur in strict subterms:\n%s"
            (metaterm_to_string term)
    | Pred(_, CoSmaller _i) | Pred(_, CoEqual _i) ->
        failwithf "Co-Inductive restrictions must not be present:\n%s"
          (metaterm_to_string term)
    | _ -> ()
  in
  aux term false

let toplevel_bindings stmt =
  let rec aux = function
    | Binding(Forall, tids, t) -> tids @ (aux t)
    | Binding(Nabla, tids, t) -> tids @ (aux t)
    | _ -> []
  in
  aux stmt

let type_apply_withs stmt ws =
  let bindings = toplevel_bindings stmt in
  List.map
    (fun (id, t) ->
       try
         let ty = List.assoc id bindings in
         (id, type_uterm ~expected_ty:ty ~sr:!sr ~sign:!sign ~ctx:sequent.vars t)
       with
       | Not_found -> failwithf "Unknown variable %s" id)
    ws

let partition_obligations ?depth obligations =
  List.partition_map begin fun g ->
    (* Format.eprintf "before search:@.%a@." *)
    (*   format_sequent_with_goal g ; *)
    let wit = search_goal_witness ?depth g WMagic in
    ensure_no_logic_variable g ;
    match wit with
    | None ->
        (* Format.eprintf "after search/failure:@.%a@." *)
        (*   format_sequent_with_goal g ; *)
        Either.Left g
    | Some w ->
        (* Format.eprintf "after search/success:@.%a@." *)
        (*   format_sequent_with_goal g ; *)
        Either.Right (g, w)
  end obligations

let apply ?depth ?name ?(term_witness=ignore) h args ws =
  let stmt = get_stmt_clearly h in
  let args = List.map get_arg_clearly args in
  let () = List.iter (Option.fold ~some:ensure_no_restrictions ~none:()) args in
  let ws = type_apply_withs stmt ws in
  let result, obligations =
    Tactics.apply_with ~sr:!sr stmt args ws
      ~used:(List.filter is_uninstantiated sequent.vars)
  in
  let remaining_obligations, term_witnesses =
    partition_obligations ?depth obligations
  in
  let () = ensure_no_logic_variable result in
  let () = List.iter term_witness term_witnesses in
  let obligation_subgoals = List.map goal_to_subgoal remaining_obligations in
  let resulting_case = recursive_metaterm_case ~used:sequent.vars ~sr:!sr result in
  begin match resulting_case with
  | None -> add_subgoals obligation_subgoals
  | Some case ->
      let resulting_subgoal =
        let restore = goal_to_subgoal sequent.goal in
        fun () ->
          restore () ;
          List.iter add_if_new_var case.stateless_new_vars ;
          List.iter (add_hyp ?name) case.stateless_new_hyps
      in
      add_subgoals ~mainline:resulting_subgoal obligation_subgoals
  end ;
  next_subgoal ()

(* Bachchain *)

let type_backchain_withs stmt ws =
  let bindings = toplevel_bindings stmt in
  let nctx = List.map term_to_pair (metaterm_support sequent.goal) in
  List.map
    (fun (id, t) ->
       try
         let ty = List.assoc id bindings in
         (id, type_uterm ~expected_ty:ty ~sr:!sr ~sign:!sign
            ~ctx:(nctx @ sequent.vars) t)
       with
       | Not_found -> failwithf "Unknown variable %s" id)
    ws

let backchain ?depth ?(term_witness=ignore) h ws =
  let stmt = get_stmt_clearly h in
  let ws = type_backchain_withs stmt ws in
  let obligations = Tactics.backchain_with ~sr:!sr stmt ws sequent.goal in
  let remaining_obligations, term_witnesses =
    partition_obligations ?depth obligations
  in
  let () = List.iter term_witness term_witnesses in
  let obligation_subgoals = List.map goal_to_subgoal remaining_obligations in
  add_subgoals obligation_subgoals ;
  next_subgoal ()

(* Case analysis *)

(* Lifting during case analysis may cause some variables to be bound to
   themselves. We need to update sequent.vars to reflect this. *)
let update_self_bound_vars () =
  sequent.vars <-
    sequent.vars |> List.map
      (fun (id, term) ->
         match term_head term with
         | Some (v, _) when term_to_name v = id ->
             (id, v)
         | _ -> (id, term))

let case_to_subgoal ?name case =
  let saved_sequent = copy_sequent () in
  fun () ->
    set_sequent saved_sequent ;
    List.iter add_if_new_var case.new_vars ;
    List.iter (add_hyp ?name) case.new_hyps ;
    Term.set_bind_state case.bind_state ;
    update_self_bound_vars ()

let case_subgoals str =
  let global_support =
    (List.flatten_map metaterm_support
       (List.map (fun h -> h.term) sequent.hyps)) @
    (metaterm_support sequent.goal)
  in
  let term = get_stmt_clearly str in
  let (mutual, defs) = def_unfold term in
  Tactics.case ~used:sequent.vars ~sr:!sr ~clauses:!clauses
    ~mutual ~defs ~global_support term

let case ?name h =
  let cases = case_subgoals h in
  (* Output.msg_printf "case: there were %d new subgoals" (List.length cases) ; *)
  add_subgoals (List.map (case_to_subgoal ?name) cases) ;
  next_subgoal ()

(* Induction *)

let next_restriction () =
  1 + (sequent.hyps |> List.map (fun h -> h.term) |>
       List.map get_max_restriction |> List.max)

let rec nth_product n term =
  match term with
  | Binding(Forall, _, body) -> nth_product n body
  | Binding(Nabla, _, body) -> nth_product n body
  | Arrow(left, right) ->
      if n = 1 then
        left
      else
        nth_product (n-1) right
  | _ -> failwith "Can only induct on predicates and judgments"

let ensure_is_inductive term =
  match term with
  | Obj _ -> ()
  | Pred(p, _) ->
      let pname = term_head_name p in
      begin try
        match (H.find defs_table pname).flavor with
        | Inductive -> ()
        | CoInductive ->
            failwithf "Cannot induct on %s since it has\
                     \ been coinductively defined"
              pname
      with Not_found ->
        failwithf "Cannot induct on %s since it has not been defined" pname
      end
  | _ -> failwith "Can only induct on predicates and judgments"

let add_ih h =
  add_hyp ~name:(fresh_hyp_name "IH") h

let induction ?name ind_args =
  if has_coinductive_restriction sequent.goal then
    failwith "Induction within coinduction is not allowed" ;
  let stmts = and_to_list sequent.goal in
  if List.length ind_args != List.length stmts then
    failwithf "Expecting %d induction arguments but got %d"
      (List.length stmts) (List.length ind_args) ;
  List.iter
    (fun (arg, goal) -> ensure_is_inductive (nth_product arg goal))
    (List.combine ind_args stmts) ;
  let res_num = next_restriction () in
  let (ihs, new_goal) = Tactics.induction ind_args res_num sequent.goal in
  let name = match name with
    | None -> fresh_hyp_name "IH"
    | Some name -> name
  in
  List.iter (add_hyp ~name) ihs ;
  sequent.goal <- new_goal


(* CoInduction *)

let rec conclusion term =
  match term with
  | Binding(Forall, _, body) -> conclusion body
  | Binding(Nabla, _, body) -> conclusion body
  | Arrow(_left, right) -> conclusion right
  | Pred(p, _) -> p
  | _ -> failwith "Cannot coinduct on a goal of this form"

let ensure_is_coinductive p =
  let pname = term_head_name p in
  try
    match (H.find defs_table pname).flavor with
    | CoInductive -> ()
    | Inductive ->
        failwithf "Cannot coinduct on %s since it has\
                 \ been inductively defined"
          pname
  with Not_found ->
    failwithf "Cannot coinduct on %s since it has not been defined" pname

let coinduction ?name () =
  ensure_is_coinductive (conclusion sequent.goal) ;
  if has_inductive_restriction sequent.goal then
    failwith "Coinduction within induction is not allowed" ;
  let res_num = next_restriction () in
  let (ch, new_goal) = Tactics.coinduction res_num sequent.goal in
  let name = match name with
    | None -> fresh_hyp_name "CH"
    | Some name -> name
  in
  add_hyp ~name ch ;
  sequent.goal <- new_goal


(* Assert *)

let delay_mainline ?name ?depth new_hyp detour_goal =
  if depth <> Some 0 && search_goal ?depth detour_goal then
    add_hyp ?name new_hyp
  else
  let mainline =
    case_to_subgoal ?name
      { bind_state = get_bind_state () ;
        new_vars = [] ;
        new_hyps = [new_hyp] }
  in
  let detour = goal_to_subgoal detour_goal in
  (* Using add_subgoals to take care of annotations *)
  add_subgoals ~mainline [detour] ;
  next_subgoal ()

let assert_hyp ?name ?depth term =
  let term = type_umetaterm ~sr:!sr ~sign:!sign ~ctx:sequent.vars term in
  delay_mainline ?name ?depth term term

(* Object logic monotone *)

let monotone ?name h t =
  let ht = get_stmt_clearly h in
  match ht with
  | Obj (obj, r) ->
      let ntids = metaterm_nominal_tids ht in
      let ctx = sequent.vars @
                (List.map (fun (id, ty) -> (id, nominal_var id ty)) ntids)
      in
      let t = type_uterm ~expected_ty:olistty ~sr:!sr ~sign:!sign ~ctx t in
      let new_obj = {obj with context = Context.normalize [t]} in
      delay_mainline ?name
        (Obj (new_obj, r))
        (Binding(Forall, [("X", oty)],
                 Arrow(member (Term.const "X" oty)
                         (Context.context_to_term obj.context),
                       member (Term.const "X" oty)
                         t))) ;
  | _ ->
      failwith "The monotone command can only be used on hypotheses of the form {...}"


(* Theorem *)

let theorem thm =
  sequent.goal <- thm


(* Introduction of forall variables *)

let intros hs =
  let rec aux hs term =
    match term with
    | Binding(Forall, bindings, body) ->
        let support = metaterm_support body in
        let (alist, vars) =
          fresh_raised_alist ~sr:!sr ~tag:Eigen ~used:sequent.vars
            ~support bindings
        in
        List.iter add_var (List.map term_to_pair vars) ;
        aux hs (replace_metaterm_vars alist body)
    | Binding(Nabla, bindings, body) ->
        let (ids, tys) = List.split bindings in
        aux hs (replace_metaterm_vars
                  (List.combine ids (fresh_nominals tys body))
                  body)
    | Arrow(left, right) -> begin
        let (name, hs) = match hs with
          | [] -> (None, [])
          | "_" :: hs -> (None, hs)
          | h :: hs -> (Some h, hs)
        in
        add_hyp ?name (normalize left) ;
        aux hs right
      end
    | _ -> term
  in
  sequent.goal <- aux hs sequent.goal

(* Split *)

let split ?name propogate_result =
  let rec accum_goals conjs prev =
    match conjs with
    | [] -> []
    | g::rest ->
        let saved = goal_to_subgoal g in
        let subgoal () =
          saved () ;
          if propogate_result then
            List.iter (add_hyp ?name) (List.rev prev)
        in
        subgoal :: (accum_goals rest (g :: prev))
  in
  let conjs = and_to_list sequent.goal in
  if List.length conjs = 1 then failwith "Needless use of split" ;
  add_subgoals (accum_goals conjs []) ;
  next_subgoal ()

(* Split theorem *)

let decompose_forall_nabla t =
  match t with
  | Binding(Forall, foralls, Binding(Nabla, nablas, body)) ->
      (foralls, nablas, body)
  | Binding(Forall, foralls, body) ->
      (foralls, [], body)
  | Binding(Nabla, nablas, body) ->
      ([], nablas, body)
  | _ ->
      ([], [], t)

let multiarrow arrows body =
  let rec aux = function
    | h::hs -> Arrow(h, aux hs)
    | [] -> body
  in
  aux arrows

(*
(* [#161] This check does not appear to be logically justified *)
let ensure_no_renaming vars terms =
  let conflicts =
    List.intersect
      vars
      (List.map fst (all_tids (List.flatten_map collect_terms terms)))
  in
  if conflicts <> [] then
    bugf "Variable renaming required"
*)

let split_theorem (tys, thm) =
  let foralls, nablas, body = decompose_forall_nabla thm in
  let arrows, conj = decompose_arrow body in
  let nabla_consts = List.map (fun (x, ty) -> const x ty) nablas in
  let lift t =
    let iforalls, inablas, ibody = decompose_forall_nabla t in
    (* Raise iforalls over nablas *)
    let alist, iforall_vars =
      fresh_raised_alist ~used:[] ~sr:!sr ~tag:Constant
        ~support:nabla_consts iforalls
    in
    let iforalls = List.map (fun x -> (term_to_name x, tc [] x)) iforall_vars in
    let ibody = replace_metaterm_vars alist ibody in
    (* [#161] This prevents things like: forall x, (forall x, p x) -> p x *)
    (*        even though they can be manually stated as new theorems *)
    (* ensure_no_renaming (List.map fst (iforalls @ inablas)) arrows ; *)
    let thm = forall (foralls @ iforalls)
        (nabla (nablas @ inablas)
           (multiarrow arrows ibody)) in
    (tys, thm)
  in
  List.map lift (and_to_list conj)

let create_split_theorems name names =
  let thms = split_theorem (get_generic_lemma name) in
  let rec loop = function
    | n::ns, t::ts, count ->
        (n, t) :: (loop (ns, ts, count+1))
    | [], t::ts, count ->
        (name ^ (string_of_int count), t) :: (loop ([], ts, count+1))
    | _ -> []
  in
  if List.length thms = 1 then
    failwith "Cannot split this type of theorem" ;
  loop (names, thms, 1)

(* Left and right side of disjunction *)

let left () =
  match sequent.goal with
  | Or(left, _) -> sequent.goal <- left
  | _ -> ()

let right () =
  match sequent.goal with
  | Or(_, right) -> sequent.goal <- right
  | _ -> ()


(* Unfold *)

let unfold clause_sel sol_sel =
  let mdefs = def_unfold sequent.goal in
  let used = sequent.vars in
  let goal = unfold ~sr:!sr ~used ~mdefs clause_sel sol_sel sequent.goal in
  let goals = List.concat (List.map and_to_list goal) in
  add_subgoals (List.map goal_to_subgoal goals) ;
  next_subgoal ()

(* Exists *)

let rec resolve_ewitness ew tids =
  match ew, tids with
  | ETerm t, ((id, ty) :: tids) ->
      (id, ty, t, tids)
  | ESub (x, t), ((id, ty) :: tids) ->
      if x = id then (x, ty, t, tids) else
      let (_, xty, _, tids) = resolve_ewitness ew tids in
      (x, xty, t, (id, ty) :: tids)
  | _, [] ->
      failwithf "Could not resolve existential witness %s" (ewitness_to_string ew)

let exists ew =
  match sequent.goal with
  | Binding (Metaterm.Exists, tids, body) ->
      let (id, ty, t, tids) = resolve_ewitness ew tids in
      let ntids = metaterm_nominal_tids body in
      let ctx = sequent.vars @
                (List.map (fun (id, ty) -> (id, nominal_var id ty)) ntids)
      in
      let t = type_uterm ~expected_ty:ty ~sr:!sr ~sign:!sign ~ctx t in
      let goal = replace_metaterm_vars [(id, t)] (exists tids body) in
      sequent.goal <- goal ;
      normalize_sequent ()
  | _ -> ()

(* Compute: see compute.ml *)

(* Skip *)

let skip () =
  skip_seen := true ;
  next_subgoal ()

(* Clear *)

let remove_var cm h =
  let v = term_to_var (List.assoc h sequent.vars) in
  sequent.vars <- List.filter (fun xv -> fst xv <> h) sequent.vars ;
  match cm with
  | Clear_extro ->
      let goal = replace_metaterm_vars [h, var Constant v.Term.name v.ts v.ty] sequent.goal in
      sequent.goal <- forall [v.Term.name, v.ty] goal
  | _ -> ()

let remove_thing cm h =
  if is_hyp h
  then remove_hyp cm h
  else remove_var cm h

let is_used v =
  List.exists begin fun h ->
    get_metaterm_used h.term |>
    List.exists (fun xv -> fst xv = v)
  end sequent.hyps

let check_removable h =
  if not (is_hyp h) then
    try
      let v = List.assoc h sequent.vars in
      if is_uninstantiated (h, v) && is_used h then
        failwithf "Cannot clear strict uninstantiated variable %s" h
    with Not_found ->
      failwithf "Unknown hypothesis or variable %s" h

let clear cm hs =
  List.iter begin fun h ->
    check_removable h ;
    remove_thing cm h ;
  end hs

(* Abbrev *)

let abbrev ids str =
  sequent.hyps <-
    List.map begin fun h ->
      if Iset.mem h.id ids then
        {h with abbrev = Some str}
      else h
    end sequent.hyps

let unabbrev ids =
  sequent.hyps <-
    List.map begin fun h ->
      if Iset.mem h.id ids then
        {h with abbrev = None}
      else h
    end sequent.hyps

(* Rename *)

let rename_hyp hfr hto =
  let hyps = List.map begin
      fun h ->
        if h.id = hfr then
          { h with id = hto }
        else h
    end sequent.hyps
  in sequent.hyps <- hyps

let rename_var vfr xto =
  let ty = tc [] (List.assoc vfr sequent.vars) in
  let vto = var Eigen xto 0 ty in
  let repl = [vfr, vto] in
  let rewrite mt = replace_metaterm_vars repl mt in
  sequent.hyps <-
    List.map (fun h -> { h with term = rewrite h.term }) sequent.hyps ;
  sequent.vars <-
    List.filter_map begin fun v ->
      let (x, _) = v in
      if x = vfr then Some (xto, vto)
      else if x = xto then None
      else Some v
    end sequent.vars ;
  sequent.goal <- rewrite sequent.goal

let var_unavailable x =
  try is_uninstantiated (x, List.assoc x sequent.vars)
  with Not_found -> false

let rename xfr xto =
  if H.mem lemmas xto then
    failwithf "%S already refers to a lemma" xto ;
  if List.exists (fun h -> h.id = xto) sequent.hyps then
    failwithf "%S already refers to an existing hypothesis" xto ;
  if var_unavailable xto then
    failwithf "%S already refers to an existing variable" xto ;
  if List.exists (fun h -> h.id = xfr) sequent.hyps then
    rename_hyp xfr xto
  else if List.mem_assoc xfr sequent.vars then
    rename_var xfr xto
  else
    failwithf "Unknown variable or hypothesis label %S" xfr

(* Permute *)

let permute_nominals ids form =
  if not (List.is_unique ids) then failwith "Not a permutation" ;
  let term =
    match form with
    | None -> sequent.goal
    | Some h ->
        try get_hyp h
        with _ -> failwithf "Unknown hypothesis %s" h
  in
  let support_alist =
    List.map (fun t -> (term_to_name t, t)) (metaterm_support term)
  in
  let perm = List.map begin fun id ->
      try List.assoc id support_alist
      with Not_found -> nominal_var id (tybase (atybase ""))
    end ids in
  let result = Tactics.permute_nominals perm term in
  match form with
  | None -> sequent.goal <- result
  | Some hyp -> replace_hyp hyp result

(* Object level cut with explicit cut formula*)

let cut_from ?name h arg term =
  let term = type_uterm ~sr:!sr ~sign:!sign ~ctx:sequent.vars term in
  let h = get_stmt_clearly h in
  let arg = get_stmt_clearly arg in
  match h, arg with
  | Obj(obj_h1, _),Obj(obj_h2, _) ->
      add_hyp ?name (object_cut_from obj_h1 obj_h2 term)
  | _,_ -> failwith "The cut command can only be used on \
                   \ hypotheses of the form {...}"

(* Saturate *)

exception SaturateSuccess
let is_ground f = metaterm_vars_alist Logic f = []
let saturate ?name ?depth ?use () =
  let use = match use with
    | None -> H.to_seq_keys lemmas
    | Some use -> List.to_seq use
  in
  let lemtab = H.create 19 in
  Seq.iter begin fun lem ->
    H.add lemtab lem (get_lemma lem)
  end use ;
  let initial_focus = H.to_seq_values lemtab |> List.of_seq in
  let depth0 = match depth with
    | None -> 1
    | Some depth -> depth
  in
  (* [%trace 2 "@[<v2>using lemmas:@,@[<b0>%t@]@]"] begin fun ff -> *)
  (*   H.iter begin fun lemname lem -> *)
  (*     Format.fprintf ff "%s:(@[%a@])@," lemname format_metaterm lem *)
  (*   end lemtab *)
  (* end ; *)
  let global_support =
    (List.flatten_map (fun h -> metaterm_support h.term) sequent.hyps @
     metaterm_support sequent.goal)
    |> List.unique ~cmp:eq
  in
  let rec loop ~depth =
    (* [%trace 2 "loop %d"] depth ; *)
    if depth <= 0 then () else begin
      let num_released, subgoals =
        multifocus [] initial_focus
          ~succ:(fun () -> loop ~depth:(depth - 1))
      in
      if num_released = 0 then begin
        [%trace 2 "Saturated at depth %d"] (depth0 - depth) ;
        ()
      end else begin
        add_subgoals subgoals ;
        next_subgoal ()
      end
    end
  and multifocus ~succ dead live =
    match live with
    | [] ->
        let to_release =
          List.rev_filter_map begin fun form ->
            if not @@ is_ground form then None else
            match purepos ~succ:(fun () -> raise SaturateSuccess) form with
            | _ ->
                (* [%trace 2 "NEW: %a"] format_metaterm form ; *)
                Some form
            | exception SaturateSuccess ->
                (* [%trace 2 "OLD: %a"] format_metaterm form ; *)
                None
          end dead in
        (* [%trace 2 "release: @[<v0>%t@]"] begin fun ff -> *)
        (*   List.iter (fun r -> Format.fprintf ff "%a@," format_metaterm r) *)
        (*     to_release *)
        (* end ; *)
        let num_released = List.length to_release in
        (num_released, release ~succ ~nvs:[] ~nhs:[] to_release)
    | form :: live -> begin
        (* [%trace 2 "multifoc %d:@ %a"] depth format_metaterm form ; *)
        match form with
        | True -> multifocus ~succ dead live
        | Arrow (f1, f2) ->
            let cases = ref [] in
            let add_proof () =
              let f1 = Metaterm.map_terms Term.deep_copy f1 in
              let f2 = Metaterm.map_terms Term.deep_copy f2 in
              (* [%trace 2 "Found @[<b2>%a ->@ %a@]"] *)
              (*   format_metaterm f1 *)
              (*   format_metaterm f2 ; *)
              if is_ground f1 then cases := (f1, f2) :: !cases
              (* else [%trace 2 "Not adding since not ground"] *)
            in
            purepos ~succ:add_proof f1 ;
            let live = List.rev_map (fun (_, f2) -> f2) !cases @ live in
            multifocus ~succ dead live
        | Binding (Forall, vs, form) ->
            let alist =
              fresh_nameless_alist ~sr:!sr ~support:global_support
                ~tag:Logic ~ts:0 vs
            in
            let form = replace_metaterm_vars alist form in
            multifocus ~succ dead (form :: live)
        | (False | Eq _ | Binding (Exists, _, _) | And _ | Or _ | Pred _) ->
            (* [%trace 2 "multifocus done with: %a"] *)
            (*   format_metaterm form ; *)
            multifocus ~succ (form :: dead) live
        | _ ->
            [%trace 2 "deleting %a"] format_metaterm form ;
            multifocus ~succ dead live
      end
  and purepos ~succ form =
    (* [%trace 2 "purepos: %a"] format_metaterm form ; *)
    match form with
    | True -> succ ()
    | False -> ()
    | Or (f1, f2) ->
        purepos ~succ f1 ;
        purepos ~succ f2
    | And (f1, f2) ->
        purepos f1 ~succ:(fun () -> purepos ~succ f2)
    | Binding (Exists, vs, form) ->
        let alist =
          fresh_nameless_alist ~sr:!sr ~support:global_support
            ~tag:Logic ~ts:0 vs
        in
        let form = replace_metaterm_vars alist form in
        purepos ~succ form
    | Eq (t1, t2) ->
        unwind_state begin fun () ->
          if Unify.try_right_unify t1 t2 then succ ()
        end ()
    | Pred (_, cr) ->
        List.iter ~guard:unwind_state begin fun h ->
          match h.term with
          | Pred (_, hr) ->
              if satisfies hr cr then
                all_meta_right_permute_unify ~sc:succ form h.term
          | _ -> ()
        end (List.unique ~cmp:(fun h1 h2 -> h1.term = h2.term) sequent.hyps)
    | Arrow _ | Binding _ | Obj _ ->
        [%trace 2 "purpos found negative: %a"]
          format_metaterm form
  and release ~succ ~nvs ~nhs forms =
    match forms with
    | [] ->
        let nvs = List.rev nvs in
        let nhs = List.rev nhs in
        let case =
          Tactics.{ bind_state = get_bind_state () ;
                    new_vars = nvs ;
                    new_hyps = nhs } in
        (* List.iter (fun h -> [%trace 2 "release hyp: %a"] format_metaterm h) nhs ; *)
        let setup_subgoal = case_to_subgoal ?name case in
        let recur () =
          setup_subgoal () ;
          succ ()
        in
        [ recur ]
    | form :: forms -> begin
        (* [%trace 2 "release_loop: %a"] format_metaterm form ; *)
        match form with
        | True -> release ~succ ~nvs ~nhs forms
        | False -> []
        | Or (f1, f2) ->
            let state = get_scoped_bind_state () in
            let cs1 = release ~succ ~nvs ~nhs (f1 :: forms) in
            set_scoped_bind_state state ;
            let cs2 = release ~succ ~nvs ~nhs (f2 :: forms) in
            cs1 @ cs2
        | And (f1, f2) ->
            release ~succ ~nvs ~nhs (f1 :: f2 :: forms)
        | Binding (Exists, vs, form) ->
            let (alist, vars) =
              fresh_raised_alist ~sr:!sr ~support:global_support
                ~used:(nvs @ sequent.vars) ~tag:Eigen vs
            in
            let nvs = List.rev_map term_to_pair vars @ nvs in
            let form = replace_metaterm_vars alist form in
            release ~succ ~nvs ~nhs (form :: forms)
        | Eq (t1, t2) -> begin
            match Unify.try_left_unify_cpairs ~used:(nvs @ sequent.vars) t1 t2 with
            | Some cpairs ->
                let nhs = List.map (fun (t1, t2) -> Eq (t1, t2)) cpairs @ nhs in
                release ~succ ~nvs ~nhs forms
            | None ->
                []
          end
        | _ ->
            (* [%trace 2 "store: %a"] format_metaterm form ; *)
            let nhs = if List.mem form nhs then nhs else form :: nhs in
            release ~succ ~nvs ~nhs forms
      end
  in
  loop ~depth:depth0
