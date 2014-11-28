(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
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
open Unify
open Extensions

(* Variable naming utilities *)

let is_uninstantiated (x, vtm) =
  match observe (hnorm vtm) with
  | Var {Term.name=n; Term.tag=Eigen; _} when n = x -> true
  | _ -> false

let alist_to_used (_, t) = term_to_pair t

let freshen_clause ~used ~sr ?(support=[]) clause =
  let (tids,head,body) = clause in
  let (alist, vars) = fresh_raised_alist ~sr ~tag:Eigen ~used ~support tids in
    (List.map term_to_pair vars @ used,
     replace_term_vars alist head,
     List.map (replace_term_vars alist) body)

let freshen_def ~used ~sr ?(support=[]) head body =
  let tids = capital_tids [head] in
  let (alist, vars) = fresh_raised_alist ~sr ~tag:Eigen ~used ~support tids in
    (List.map term_to_pair vars,
     replace_term_vars alist head,
     replace_metaterm_vars alist body)

let term_vars_alist tag terms =
  List.map term_to_pair (find_var_refs tag terms)

let metaterm_vars_alist tag metaterm =
  term_vars_alist tag (collect_terms metaterm)

(* Freshening for Logic variables uses anonymous names *)

let fresh_nameless_alist ~support ~tag ~ts tids =
  let ntys = List.map (tc []) support in
    List.map
      (fun (x, ty) ->
         (x, app (fresh ~tag ts (tyarrow ntys ty)) support))
      tids

let freshen_nameless_clause ?(support=[]) ~ts clause =
  let (tids,head,body) = clause in
  let fresh_names = fresh_nameless_alist ~support ~tag:Logic ~ts tids in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = List.map (replace_term_vars fresh_names) body in
  (fresh_names,fresh_head, fresh_body)

let freshen_nameless_def ?(support=[]) ~ts head body =
  let tids = capital_tids [head] in
  let fresh_names = fresh_nameless_alist ~support ~tag:Logic ~ts tids in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = replace_metaterm_vars fresh_names body in
    (fresh_head, fresh_body)

let freshen_nameless_bindings ~support ~ts bindings term =
  let alist = fresh_nameless_alist ~support ~tag:Logic ~ts bindings in
    replace_metaterm_vars alist term


let existentially_close ~used quant_vars body =
  let bindings : (id * term) list ref = ref [] in
  let emit x xv = bindings := (x, xv) :: !bindings in
  let rec renumber_one stem cur v =
    let candidate = stem ^ string_of_int cur in
    if List.mem_assoc candidate used then
      renumber_one stem (cur + 1) v
    else begin
      emit v.name (Term.var Constant candidate 0 v.ty) ;
      cur
    end
  in
  List.iter begin fun (x, nvs) ->
    List.fold_left (renumber_one x) 1 nvs |> ignore
  end quant_vars ;
  match List.rev !bindings with
  | [] -> body
  | bindings ->
    let body = replace_metaterm_vars bindings body in
    let bindings =
      List.map (fun (_, xv) -> (term_to_name xv, tc [] xv))
        bindings in
    Binding (Exists, bindings, body)


(* Object level cut *)

(* obj1 = L2, A |- C
   obj2 = L1 |- A
   result = L2, L1 |- C *)
let object_cut obj1 obj2 =
  match obj1, obj2 with
  | Async obj1, Async obj2 ->
  let ctx1,term1 = Async.get obj1 in
  let ctx2,term2 = Async.get obj2 in
  if Context.mem term2 ctx1 then
    let ctx =
      ctx1
      |> Context.remove term2
      |> Context.union ctx2
      |> Context.normalize
    in
      if Context.wellformed ctx then
        Obj(Async (Async.obj ctx term1), Irrelevant)
      else
        failwith "Cannot merge contexts"
  else
    failwith "Needless use of cut"
  | _, _ ->
      failwith "Cannot use cut on sync objects"

let object_cut_from obj1 obj2 term =
  match obj1, obj2 with
  | Async obj1, Async obj2 ->
  let ctx1,term1 = Async.get obj1 in
  let cuttable tobj cut_obj =
    let tctx,tterm = Async.get tobj in
    let cctx,cterm = Async.get cut_obj in
    eq tterm cterm && Context.subcontext tctx cctx
  in
  let get_cut_ctx tobj cut_obj =
    let tctx = tobj.Async.context in
    let cctx = cut_obj.Async.context in
    List.filter_map
      (fun t -> if Context.mem t tctx then None else Some t) cctx
  in
  if Context.mem term ctx1 then
    let tobj = normalize_obj (Async (Async.obj Context.empty term)) in
    let norms = obj_support tobj in
    let nids,ntys = List.split (nominal_tids norms) in
    let cut_objs =
    List.permute (List.length norms) (obj_support (Async obj2))
      |> List.find_all
          (fun permuted -> ntys = List.map (tc []) permuted)
      |> List.filter_map
          (fun permuted ->
            let tobj =
              replace_metaterm_vars (List.combine nids permuted)
                (Obj (tobj, Irrelevant))
            in
            match tobj with
            | Obj (Async tobj,_) ->
              if cuttable tobj obj2 then
                let ctx2 = get_cut_ctx tobj obj2 in
                let ctx =
                  ctx1
                  |> Context.remove term
                  |> Context.union ctx2
                  |> Context.normalize
                in
                if Context.wellformed ctx then
                  Some (Obj(Async (Async.obj ctx term1), Irrelevant))
                else
                  None
              else
                None
            | _ -> assert false)
    in
    match cut_objs with
    | [] -> failwith "Cannot merge contexts"
    | (obj::_) -> obj
  else
    failwith "Needless use of cut"
  | _, _ ->
      failwith "Cannot use cut on sync objects"


(* Search cut *)

let search_cut ~search_goal obj =
  (* Process the context from head to tail looking for goals to remove *)
  let rec aux left right =
    match right with
      | d::ds ->
          if search_goal (Obj(Async (Async.obj (left @ ds) d), Irrelevant)) then
            aux left ds
          else
            aux (d::left) ds
      | [] -> left
  in
  match obj with
  | Async obj ->
      let ctx,term = Async.get obj in
      Async (Async.obj (aux [] (List.rev ctx)) term)
  | Sync _ ->
      failwith "Search cut on sync objects"

(* Object level instantiation *)

(* inst t1 with n = t2 *)
let object_inst t1 n t2 =
  if List.mem n (List.map term_to_name (metaterm_support t1)) then
    map_on_objs (map_obj (replace_term_vars ~tag:Nominal [(n, t2)])) t1
  else
    failwith ("Did not find " ^ n)

(* Case analysis *)

type case = {
  bind_state : bind_state ;
  new_vars : (id * term) list ;
  new_hyps : metaterm list ;
}

type stateless_case = {
  stateless_new_vars : (id * term) list ;
  stateless_new_hyps : metaterm list ;
}

let empty_case = { stateless_new_vars = [] ; stateless_new_hyps = [] }

let stateless_case_to_case case =
  { bind_state = get_bind_state () ;
    new_vars = case.stateless_new_vars ;
    new_hyps = case.stateless_new_hyps }

let cpairs_to_eqs cpairs = List.map (fun (x,y) -> Eq(x,y)) cpairs

(* This handles asynchrony on the left *)
let rec recursive_metaterm_case ~used ~sr term =
  match normalize term with
    | True -> Some empty_case
    | False -> None
    | Eq(a, b) ->
        begin match try_left_unify_cpairs ~used a b with
          | Some cpairs ->
              Some {
                (* Names created perhaps by unification *)
                stateless_new_vars = term_vars_alist Eigen [a;b] ;
                stateless_new_hyps = cpairs_to_eqs cpairs
              }
          | None -> None
        end
    | And(left, right) ->
        begin match recursive_metaterm_case ~used ~sr left with
          | None -> None
          | Some {stateless_new_vars = vars_left ;
                  stateless_new_hyps = hyps_left } ->
              match recursive_metaterm_case ~used:(vars_left @ used) ~sr right with
                | None -> None
                | Some {stateless_new_vars = vars_right ;
                        stateless_new_hyps = hyps_right } ->
                    Some { stateless_new_vars = vars_left @ vars_right ;
                           stateless_new_hyps = hyps_left @ hyps_right }
        end
    | Binding(Exists, tids, body) ->
        let support = metaterm_support term in
        let (alist, vars) = fresh_raised_alist ~sr ~tag:Eigen ~used ~support tids in
        let fresh_body = replace_metaterm_vars alist body in
        let new_vars = List.map term_to_pair vars in
        let nested =
          recursive_metaterm_case ~used:(new_vars @ used) ~sr fresh_body
        in
          begin match nested with
            | None -> None
            | Some { stateless_new_vars = nested_vars ;
                     stateless_new_hyps = nested_hyps } ->
                Some { stateless_new_vars = new_vars @ nested_vars ;
                       stateless_new_hyps = nested_hyps }
          end
    | Binding(Nabla, ids, body) ->
        let alist = make_nabla_alist ids body in
        let fresh_body = replace_metaterm_vars alist body in
          recursive_metaterm_case ~used ~sr fresh_body
    | _ -> Some {stateless_new_vars = [] ; stateless_new_hyps = [term]}

let spine_view t =
  let tys, t =
    let t = hnorm t in
      match observe t with
        | Lam(tys, t) -> (tys, t)
        | _ -> ([], t)
  in
  let head, args =
    let t = hnorm t in
      match observe t with
        | App(head, args) -> (head, args)
        | _ -> (t, [])
  in
    (tys, head, args)

let rec is_left_flexible t =
  match observe (hnorm t) with
    | Var v -> v.tag = Eigen
    | DB _ -> false
    | Lam(_, b) -> is_left_flexible b
    | App(h, _) -> is_left_flexible h
    | _ -> assert false

let rec is_left_rigid t =
  match observe (hnorm t) with
    | Var v -> v.tag = Constant || v.tag = Nominal
    | DB _ -> true
    | Lam(_, b) -> is_left_rigid b
    | App(h, _) -> is_left_rigid h
    | _ -> assert false

let one_step_huet ~used ~sr a b =
  let flex_rigid flex rigid =
    let ftys, fhead, fargs = spine_view flex in
    let rtys, rhead, rargs = spine_view rigid in
      if List.length ftys > List.length rtys then
        []
      else
        List.filter_map
          (unwind_state
             (fun x ->
                let used = (term_vars_alist Eigen [x]) @ used in
                  if try_left_unify ~used fhead x then
                    match
                      recursive_metaterm_case ~used ~sr (Eq(flex, rigid))
                    with
                      | None -> None
                      | Some sc -> Some (stateless_case_to_case sc)
                  else
                    None))
          (left_flexible_heads ~used ~sr
             (ftys, fhead, fargs) (rtys, rhead, rargs))
  in
    if is_left_flexible a && is_left_rigid b then
      flex_rigid a b
    else if is_left_rigid a && is_left_flexible b then
      flex_rigid b a
    else
      [{ bind_state = get_bind_state () ;
         new_vars = [] ;
         new_hyps = [Eq(a, b)] }]

let rec or_to_list term =
  match term with
    | Or(left, right) -> (or_to_list left) @ (or_to_list right)
    | _ -> [term]

let rec and_to_list term =
  match term with
    | And(left, right) -> (and_to_list left) @ (and_to_list right)
    | _ -> [term]

let rec list_to_and terms =
  List.fold_left1 meta_and terms

let predicate_wrapper r names t =
  let rec aux t =
    match t with
      | True | False | Eq _ | Obj _ -> t
      | Pred(p, _) ->
          if List.mem (term_head_name p) names then
            Pred(p, reduce_inductive_restriction r)
          else
            t
      | Binding(binding, ids, body) -> Binding(binding, ids, aux body)
      | Or(t1, t2) -> Or(aux t1, aux t2)
      | And(t1, t2) -> And(aux t1, aux t2)
      | Arrow(t1, t2) -> Arrow(t1, aux t2)
  in
    aux t

let lift_all ~used ~sr nominals =
  used |> List.iter
      (fun (id, term) ->
         if is_free term then
           let v = term_to_var term in
           let rty, rvars = raise_type ~sr nominals v.ty in
           let new_term = var Eigen id v.ts rty in
             bind term (app new_term rvars))

let case ~used ~sr ~clauses ~mutual ~defs ~global_support term =
  let support = metaterm_support term in
  let def_case ~wrapper term =
    let make_case ~support ~used (head, body) term =
      let fresh_used, head, body =
        freshen_def ~sr ~support ~used head body
      in
      match try_left_unify_cpairs ~used:(fresh_used @ used) head term with
      | Some cpairs ->
        let used_head = term_vars_alist Eigen [head; term] in
        let used_body = metaterm_vars_alist Eigen body in
        let used = List.unique (used_head @ used_body @ used) in
        begin match recursive_metaterm_case ~used ~sr body with
          | None -> []
          | Some case ->
            [{ bind_state = get_bind_state () ;
               new_vars = case.stateless_new_vars @ used ;
               new_hyps =
                 cpairs_to_eqs cpairs @
                   List.map wrapper case.stateless_new_hyps }]
        end
      | None -> []
    in
    defs |> List.flatten_map
      (unwind_state
         (function
           | Pred(head, _), body ->
             make_case ~support ~used (head, body) term
           | Binding(Nabla, tids, Pred(head, _)), body ->
             List.range 0 (List.length tids) |> List.rev |> List.flatten_map
               (fun n -> (* n is the number of nablas to be raised *)
                  List.choose n tids |> List.flatten_map
                    (unwind_state
                       (fun raised ->
                          let (rids, rtys) = List.split raised in
                          let nominals =
                            (* Want freshness with respect to global support *)
                            fresh_nominals rtys (pred (app head global_support))
                          in
                          let () = lift_all ~used ~sr nominals in
                          let head = replace_term_vars (List.combine rids nominals) head in
                          let (pids, ptys) = List.split (List.minus tids raised) in
                          List.permute (List.length pids) support
                          |> List.find_all
                            (fun permuted -> ptys = List.map (tc []) permuted)
                          |> List.flatten_map
                            (unwind_state
                               (fun permuted ->
                                  let support = List.minus support permuted in
                                  let head =
                                    replace_term_vars (List.combine pids permuted) head
                                  in
                                  make_case ~support ~used (head, body) term)))))
           | _ -> failwith "Bad head in definition"))
  in

  let focus sync_obj r =
    let ctx,f,term = Sync.get sync_obj in
    if (*has_eigen_head term or*) has_eigen_head f then
      failwith "Cannot perform case-analysis on flexible head" ;
    let wrapper t =
      Obj (Async (Async.obj ctx t), reduce_inductive_restriction r)
    in
    (unwind_state
       (fun clause ->
         let fresh_used, fresh_head, fresh_body =
           freshen_clause ~sr ~support ~used clause
         in
         match try_left_unify_cpairs ~used:(fresh_used @ used)
             fresh_head term
         with
         | Some cpairs ->
             let new_vars =
               term_vars_alist Eigen (fresh_head::term::fresh_body)
             in
             let wrapped_body = List.map wrapper fresh_body in
             Some { bind_state = get_bind_state () ;
                    new_vars = new_vars ;
                    new_hyps = cpairs_to_eqs cpairs @ wrapped_body }
         | None -> None))
      (clausify f)
  in

  let clause_case async_obj r =
    let ctx,term = Async.get async_obj in
    let get_sync_obj clause = Sync.obj ctx clause term in
    List.filter_map (fun clause -> focus (get_sync_obj clause) r) clauses
  in

  (* create a sync sequent focusing on a formula
     in the context *)
  let create_sync ~used ~sr ~support async_obj r =
    let ctx,t = Async.get async_obj in
    let raise_result =
      fresh_raised_alist ~sr ~tag:Eigen ~used ~support [("F", oty)] in
    let f,fvar =
      match raise_result with
      | ([(_, f)], [fvar]) -> f,fvar
      | _ -> assert false
    in
    let sync = Sync.obj ctx f t in
    let mem = member f (Context.context_to_term ctx) in
    { bind_state = get_bind_state () ;
      new_vars = [term_to_pair fvar];
      new_hyps = [Obj (Sync sync, reduce_inductive_restriction r) ; mem] }
  in

  let async_case obj r =
    let clause_cases = clause_case obj r in
    let ctx,_ = Async.get obj in
        clause_cases @
          (if Context.is_empty ctx then []
           else [create_sync ~used ~sr ~support obj r])
  in

  let sync_case obj r =
    match focus obj r with
    | Some case -> [case]
    | None -> []
  in

    match term with
      | Obj(Async obj, r) -> async_case obj r
      | Obj(Sync obj, r)  -> sync_case obj r
      | True -> [stateless_case_to_case empty_case]
      | False -> []
      | Pred(_, CoSmaller _) -> failwith "Cannot case analyze hypothesis\
                                          \ with coinductive restriction"
      | Pred(p, r) ->
          def_case ~wrapper:(predicate_wrapper r mutual) p
      | Or _ ->
          List.filter_map
            (unwind_state
               (fun g ->
                  match recursive_metaterm_case ~used ~sr g with
                    | None -> None
                    | Some c -> Some (stateless_case_to_case c)))
            (or_to_list term)
      | Eq(a, b) ->
          begin match recursive_metaterm_case ~used ~sr term with
            | None -> []
            | Some sc ->
                match sc.stateless_new_hyps with
                  | [Eq(a', b')] when eq a a' && eq b b' ->
                      one_step_huet ~used ~sr a b
                  | _ -> [stateless_case_to_case sc]
          end
      | And _
      | Binding(Exists, _, _)
      | Binding(Nabla, _, _) ->
          Option.map_default (fun sc -> [stateless_case_to_case sc]) []
            (recursive_metaterm_case ~used ~sr term)
      | _ -> invalid_metaterm_arg term



(* Induction *)

let rec set_restriction_at res stmt arg =
  match stmt with
    | Arrow(left, right) ->
        if arg = 1 then
          Arrow(set_restriction res left, right)
        else
          Arrow(left, set_restriction_at res right (arg-1))
    | _ -> failwith "Not enough implications in induction"

let single_induction ind_arg ind_num stmt =
  let rec aux stmt =
    match stmt with
      | Binding(Forall, bindings, body) ->
          let (ih, goal) = aux body in
            (forall bindings ih, forall bindings goal)
      | Binding(Nabla, bindings, body) ->
          let (ih, goal) = aux body in
            (nabla bindings ih, nabla bindings goal)
      | term ->
          let ih = set_restriction_at (Smaller ind_num) term ind_arg in
          let goal = set_restriction_at (Equal ind_num) term ind_arg in
            (ih, goal)
  in
    aux stmt

let induction ind_args ind_num stmt =
  List.combine ind_args (and_to_list stmt)
  |> List.map (fun (arg, goal) -> single_induction arg ind_num goal)
  |> List.split
  |> fun (ihs, goals) -> (ihs, list_to_and goals)

let coinduction res_num stmt =
  let rec aux stmt =
    match stmt with
      | Binding(Forall, bindings, body) ->
          let (ch, goal) = aux body in
            (forall bindings ch, forall bindings goal)
      | Binding(Nabla, bindings, body) ->
          let (ch, goal) = aux body in
            (nabla bindings ch, nabla bindings goal)
      | Arrow(left, right) ->
          let (ch, goal) = aux right in
            (arrow left ch, arrow left goal)
      | Pred(p, Smaller _) | Pred(p, Equal _) ->
          failwith "Cannot coinduct on inductively restricted goal"
      | Pred(p, _) ->
          let ch = Pred(p, CoSmaller res_num) in
          let goal = Pred(p, CoEqual res_num) in
            (ch, goal)
      | _ -> invalid_metaterm_arg stmt
  in
    aux stmt

(* Unfold the current goal *)

let has_restriction test t =
  let rec aux t =
    match t with
      | True | False | Eq _ -> false
      | Obj(_, r) -> test r
      | Arrow(a, b) | Or(a, b) | And(a, b) -> aux a || aux b
      | Binding(_, _, body) -> aux body
      | Pred(_, r) -> test r
  in
    aux t

let has_inductive_restriction t =
  has_restriction (function | Smaller _ | Equal _ -> true | _ -> false) t

let has_coinductive_restriction t =
  has_restriction (function | CoSmaller _ | CoEqual _ -> true | _ -> false) t

let coinductive_wrapper r names t =
  let rec aux t =
    match t with
      | True | False | Eq _ | Obj _ -> t
      | Pred(p, _) ->
          if List.mem (term_head_name p) names then
            Pred(p, reduce_coinductive_restriction r)
          else t
      | Binding(binding, ids, body) -> Binding(binding, ids, aux body)
      | Or(t1, t2) -> Or(aux t1, aux t2)
      | And(t1, t2) -> And(aux t1, aux t2)
      | Arrow(t1, t2) -> Arrow(t1, aux t2)
  in
    aux t

let maybe_select sel l = match sel with
  | Abella_types.Select_any -> l
  | Abella_types.Select_num n ->
      if n > List.length l then
        failwithf "Cannot select clause #%d; there are only %d clauses" n
          (List.length l) ;
      [List.nth l (n - 1)]
  | Abella_types.Select_named n ->
      failwith "Cannot select named clauses for inductive predicates"

let unfold_defs ~mdefs clause_sel ~ts goal r =
  let p = term_head_name goal in
  let (mutual, defs) = mdefs in
  let support = term_support goal in
  let wrapper = coinductive_wrapper r mutual in
  let unfold_def tids head body i =
    let (ids, tys) = List.split tids in
      (* Add dummy nominals in case nabla bound variables aren't used *)
    let support =
      (fresh_nominals_by_list tys (List.map term_to_name support)) @
        support
    in
      support
      |> List.permute (List.length tids)
      |> List.find_all (fun nominals -> tys = List.map (tc []) nominals)
      |> List.flatten_map
          (unwind_state
             (fun nominals ->
                let support = List.minus support nominals in
                let alist = List.combine ids nominals in
                let head = replace_term_vars alist head in
                let head, body = freshen_nameless_def ~support ~ts head body in
                  match try_right_unify_cpairs head goal with
                    | None -> []
                    | Some cpairs ->
                        [(get_bind_state (), cpairs, normalize (wrapper body), i)]))
  in
    defs
    |> maybe_select clause_sel
    |> List.map
        (fun (head, body) ->
           match head with
             | Pred(h, _) -> ([], h, body)
             | Binding(Nabla, tids, Pred(h, _)) -> (tids, h, body)
             | _ -> assert false)
    |> List.find_all (fun (_, h, _) -> term_head_name h = p)
    |> List.number
    |> List.flatten_map
        (fun (i, (tids, head, body)) -> unfold_def tids head body i)

let try_unify_cpairs cpairs =
  List.for_all (curry try_right_unify) cpairs

let rec disjoin = function
  | [] -> False
  | [f] -> f
  | f1 :: f2 :: fs -> disjoin (Or (f1, f2) :: fs)

let unfold ~mdefs ~used clause_sel sol_sel goal0 =
  match goal0 with
  | Pred(_, Smaller _) | Pred(_, Equal _) ->
      failwith "Cannot unfold inductively restricted predicate"
  | Pred(goal, r) ->
      (* Find the first body without lingering conflict pairs *)
      let rec select_non_cpairs emit list =
        match list with
        | (state, [], body, _)::rest ->
            set_bind_state state;
            select_non_cpairs (Metaterm.map_terms Term.deep_copy body :: emit) rest
        | _::rest -> select_non_cpairs emit rest
        | [] -> emit
      in
      let unfoldings = unfold_defs ~mdefs clause_sel ~ts:0 goal r in
      begin match select_non_cpairs [] unfoldings with
        | [] -> failwith "No matching clauses"
        | [case1] -> [case1]
        | cases -> begin
            let cases = List.rev cases in
            match sol_sel with
            | Abella_types.Solution_first -> [List.hd cases]
            | Abella_types.Solution_all -> [disjoin cases]
          end
      end
  | Obj (Async goal, sr) -> begin
      match clause_sel with
      | Abella_types.Select_named nm -> begin
          match Typing.lookup_clause nm with
          | Some cl -> begin
              let goal = match normalize_obj (Async goal) with
                | Async goal -> goal
                | _ -> assert false
              in
              let support = metaterm_support goal0 in
              let (vars, head, body) = freshen_nameless_clause ~support ~ts:0 (clausify cl) in
              match try_right_unify_cpairs head goal.Async.term with
              | None -> failwithf "Head of program clause named %S not unifiable with goal" nm
              | Some cpairs ->
                  if try_unify_cpairs cpairs then begin
                    let new_vars = List.map (fun (x, xv) -> (x, find_vars Logic [xv])) vars in
                    let quant_vars =
                      List.fold_left
                        (fun vs (x, nvs) -> if nvs = [] then vs else (x, nvs) :: vs)
                        [] new_vars in
                    let body =
                      List.map (fun g -> Obj (Async (Async.obj goal.Async.context g) |> normalize_obj, sr))
                        body in
                    if quant_vars = [] then body
                    else [existentially_close ~used quant_vars (conjoin body)]
                  end else
                    failwithf "Unsolvable unification of head of program clause named %S with goal" nm
            end
          | None -> failwithf "Program clause named %S not found" nm
        end
      | _ ->
          failwith "Can only unfold named program clauses for object sequents"
    end
  | Obj (Sync _, _) ->
      failwith "Cannot unfold backchaining sequents"
  | _ ->
      failwith "Cannot unfold this kind of goal"

(* Search *)

type witness =
  | WTrue
  | WHyp of id
  | WLeft of witness
  | WRight of witness
  | WSplit of witness * witness
  | WIntros of id list * witness
  | WExists of (id * term) list * witness
  | WReflexive
  | WUnfold of id * int * witness list

let witness_to_string =
  let bind_to_string (id, t) =
    id ^ " = " ^ (term_to_string t)
  in

  let rec aux = function
    | WTrue -> "true"
    | WHyp id -> id
    | WLeft w -> "left(" ^ aux w ^ ")"
    | WRight w -> "right(" ^ aux w ^ ")"
    | WSplit(w1, w2) -> "split(" ^ aux w1 ^ ", " ^ aux w2 ^ ")"
    | WIntros(ids, w) ->
        "intros[" ^ (String.concat ", " ids) ^ "](" ^ aux w ^ ")"
    | WExists(binds, w) ->
        "exists[" ^ (String.concat ", " (List.map bind_to_string binds)) ^
          "](" ^ aux w ^ ")"
    | WReflexive -> "reflexive"
    | WUnfold(id, n, ws) ->
        let body = if ws = [] then "" else "(" ^ aux_list ws ^ ")" in
          id ^ "[" ^ (string_of_int n) ^ "]" ^ body

  and aux_list ws =
    String.concat ", " (List.map aux ws)
  in
    aux

exception SearchSuccess of witness

let decompose_arrow term =
  let rec aux acc term =
    match term with
      | Arrow(a, b) -> aux (a::acc) b
      | _ -> (List.rev acc, term)
  in
    aux [] term

let assoc_mdefs name alldefs =
  try
    List.find (fun (ids, defs) -> List.mem name ids) alldefs
  with Not_found ->
    ([], [])

let alist_to_ids alist =
  List.map term_to_string (List.map snd alist)

let satisfies r1 r2 =
  match r1, r2 with
    | CoSmaller i, CoSmaller j when i = j -> true
    | CoSmaller _, _ -> false

    | Smaller i, Smaller j
    | Smaller i, Equal j
    | Equal i, Equal j when i = j -> true

    | _, Smaller _ -> false
    | _, Equal _ -> false

    | _ -> true


(** Search

  - Depth is decremented only when unfolding clauses and definitions since
    only these can cause infinite search

  - Each aux search returns () on failure and calls (sc w) on success where
    w is a witness. This allows for effective backtracking.
    sc means success continuation.
*)

let search ~depth:n ~hyps ~clauses ~alldefs
    ?(sc=fun w -> raise (SearchSuccess w)) goal =

  let temporary_hyp_name =
    let count = ref 0 in
      fun () ->
        incr count ;
        "h" ^ (string_of_int !count)
  in

  let rec clause_aux n context foci goal r ts ~sc =
    let support = term_list_support (goal :: context) in
    let freshen_clause cl =
      let (_vars, head, body) = freshen_nameless_clause ~support ~ts cl in
      (head, body)
    in
    let p = term_head_name goal in
    let wrap body = List.map (fun t -> Async.obj context t) body in
      foci
      (* ignore the elements in the context of type olist *)
      |> List.find_all (fun cls -> not (tc [] cls = olistty))
      |> List.map clausify
      |> List.find_all (fun (_, h, _) -> term_head_name h = p)
      |> List.map freshen_clause
      |> List.number
      |> List.iter
          (unwind_state
             (fun (i, (head, body)) ->
                match try_right_unify_cpairs head goal with
                  | None ->
                      ()
                  | Some cpairs ->
                      async_obj_aux_conj (n-1) (wrap body) r ts
                        ~sc:(fun ws -> if try_unify_cpairs cpairs then
                               sc (WUnfold(p, i, ws)))))

  and async_obj_aux n hyps goal r ts ~sc =
    let gresult = normalize_obj (Async goal) in
    let goal =
      match gresult with
      | (Async goal) -> goal
      | _ -> assert false
    in
      (* Check hyps for derivability *)
      hyps
      |> List.find_all (fun (id, h) -> is_async_obj h)
      |> List.find_all (fun (id, h) -> satisfies (term_to_restriction h) r)
      |> List.map (fun (id, h) -> (id, term_to_async_obj h))
      |> List.iter
          (unwind_state
             (fun (id, obj) ->
               if derivable_async goal obj then sc (WHyp id))) ;

      match r with
        | Smaller _ | Equal _ -> ()
        | _ ->
            (* Backchain *)
            let ctx,term = Async.get goal in
            if n > 0 then clause_aux n ctx (ctx @ clauses) term r ts ~sc;
            (* Also backchain the goal G in '{.. L ..|- G}' on clauses F 
               occurring in hypotheses of the form 'member F L' *)
            let ctxs = List.find_all (fun cls -> tc [] cls = olistty)
                goal.Async.context in
            let get_member_foci hyp =
              if is_member hyp then
                let e,ctx = extact_member hyp in
                if Context.mem ctx ctxs then Some e else None
              else
                None
            in
            let ctx_focis = List.filter_map get_member_foci
                (List.map (fun (id,h) -> h) hyps) in
            let focus_goals = List.map
                (fun fc -> Sync.obj ctx fc term) ctx_focis in
            List.iter (fun fg -> sync_obj_aux n hyps fg r ts ~sc) focus_goals

  and sync_obj_aux n hyps goal r ts ~sc =
    let gresult = normalize_obj (Sync goal) in
    let goal =
      match gresult with
      | (Sync goal) -> goal
      | _ -> assert false
    in
    (* Check hyps for derivability *)
    hyps
      |> List.find_all (fun (id, h) -> is_sync_obj h)
      |> List.find_all (fun (id, h) -> satisfies (term_to_restriction h) r)
      |> List.map (fun (id, h) -> (id, term_to_sync_obj h))
      |> List.iter
          (unwind_state
             (fun (id, obj) ->
               if derivable_sync goal obj then sc (WHyp id))) ;

      match r with
        | Smaller _ | Equal _ -> ()
        | _ ->
            let ctx,focus,term = Sync.get goal in
            if n > 0 then clause_aux n ctx [focus] term r ts ~sc

  and async_obj_aux_conj n goals r ts ~sc =
    match goals with
      | [] -> sc []
      | g::gs -> async_obj_aux n hyps g r ts
          ~sc:(fun w -> async_obj_aux_conj n gs r ts ~sc:(fun ws -> sc (w::ws)))

  and metaterm_aux n hyps goal ts ~sc =
    let goal = normalize goal in

    hyps |> List.iter
        (unwind_state
           (fun (id, hyp) ->
              if (match hyp, goal with
                    | Pred(_, rh), Pred(_, rg)
                    | Obj(_, rh), Obj(_, rg) -> satisfies rh rg
                    | _ -> true) then
                all_meta_right_permute_unify ~sc:(fun () -> sc (WHyp id)) goal hyp)) ;

    match goal with
      | True -> sc WTrue
      | False -> ()
      | Eq(left, right) ->
          unwind_state
            (fun () -> if try_right_unify left right then sc WReflexive)
            ()
      | Or(left, right) ->
          metaterm_aux n hyps left ts ~sc:(fun w -> sc (WLeft w)) ;
          metaterm_aux n hyps right ts ~sc:(fun w -> sc (WRight w))
      | And(left, right) ->
          metaterm_aux n hyps left ts
            ~sc:(fun w1 -> metaterm_aux n hyps right ts
                   ~sc:(fun w2 -> sc (WSplit(w1,w2))))
      | Arrow _ ->
          let (args, body) = decompose_arrow goal in
          let args = List.map (fun h -> (temporary_hyp_name (), h)) args in
          metaterm_aux n (args @ hyps) body ts
            ~sc:(fun w -> sc (WIntros(List.map fst args, w)))
      | Binding(Exists, tids, body) ->
          let global_support =
            List.unique
              ((List.flatten_map (fun (_, h) -> metaterm_support h) hyps) @
                 (metaterm_support goal))
          in
          let alist = fresh_nameless_alist
            ~support:global_support ~tag:Logic ~ts tids
          in
          let body = replace_metaterm_vars alist body in
            metaterm_aux n hyps body ts ~sc:(fun w -> sc (WExists(alist, w)))
      | Binding(Nabla, tids, body) ->
          let alist = make_nabla_alist tids body in
          let body = replace_metaterm_vars alist body in
            metaterm_aux n hyps body ts
              ~sc:(fun w -> sc (WIntros(alist_to_ids alist, w)))
      | Binding(Forall, tids, body) ->
          let ts = ts + 1 in
          let alist = fresh_nameless_alist ~support:[] ~tag:Eigen ~ts tids in
          let body = replace_metaterm_vars alist body in
            metaterm_aux n hyps body ts
              ~sc:(fun w -> sc (WIntros(alist_to_ids alist, w)))
      | Obj(Async obj, r) -> async_obj_aux n hyps obj r ts ~sc
      | Obj(Sync obj, r) -> sync_obj_aux n hyps obj r ts ~sc
      | Pred(_, Smaller _) | Pred(_, Equal _) -> ()
      | Pred(p, r) -> if n > 0 then def_aux n hyps p r ts ~sc

  and def_aux n hyps goal r ts ~sc =
    let p = term_head_name goal in
    let mdefs = assoc_mdefs p alldefs in
      unwind_state
        (fun () ->
           unfold_defs ~mdefs Abella_types.Select_any ~ts goal r |> List.iter
               (fun (state, cpairs, body, i) ->
                  set_bind_state state ;
                  metaterm_aux (n-1) hyps body ts
                    ~sc:(fun w -> if try_unify_cpairs cpairs then
                           sc (WUnfold(p, i, [w])))))
        ()

  in
    try
      metaterm_aux n hyps goal 0 ~sc ;
      None
    with SearchSuccess(w) -> Some w

(* Apply one statement to a list of other statements *)

let check_restrictions formal actual =
  if (List.length formal <> List.length actual) then
    failwithf "%s arguments to apply" begin
      let diff = compare (List.length formal) (List.length actual) in
      if diff > 0 then "Not enough" else "Too many"
    end ;
  List.iter2 (fun fr ar -> match fr, ar with
                | Smaller i, Smaller j when i = j -> ()
                | Equal i, Smaller j when i = j -> ()
                | Equal i, Equal j when i = j -> ()
                | Irrelevant, _ -> ()
                | _ -> failwith "Inductive restriction violated")
    formal actual

let rec map_args f t =
  match t with
    | Arrow(left, right) ->
        (f left) :: (map_args f right)
    | _ -> []

let some_term_to_restriction t =
  match t with
    | None -> Irrelevant
    | Some t -> term_to_restriction t

let apply_arrow term args =
  let () = check_restrictions
    (map_args term_to_restriction term)
    (List.map some_term_to_restriction args)
  in
  let context_pairs = ref [] in
  let obligations = ref [] in
  let result =
    List.fold_left
      (fun term arg ->
         match term, arg with
           | Arrow(Obj(Async left, _), right), Some Obj(Async arg, _) ->
               let lft_ctx,lft_term = Async.get left in
               let arg_ctx,arg_term = Async.get arg in
               context_pairs := (lft_ctx, arg_ctx)::!context_pairs ;
               right_unify lft_term arg_term ;
               right
           | Arrow(Obj(Sync left, _), right), Some Obj(Sync arg, _) ->
               let lft_ctx,lft_f,lft_term = Sync.get left in
               let arg_ctx,arg_f,arg_term = Sync.get arg in
               context_pairs := (lft_ctx, arg_ctx)::!context_pairs ;
               right_unify lft_f arg_f ;
               right_unify lft_term arg_term ;
               right
           | Arrow(left, right), Some arg ->
               meta_right_unify left arg ;
               right
           | Arrow(left, right), None ->
               obligations := left::!obligations ;
               right
           | _ -> failwith "Too few implications in application")
      term
      args
  in
    Context.reconcile !context_pairs ;
    (normalize result, !obligations)

let apply ?(used_nominals=[]) term args =
  let support =
    Some term :: args
    |> List.flatten_map (Option.map_default metaterm_support [])
    |> List.unique
    |> fun s -> List.minus s used_nominals
  in
  let process_bindings foralls nablas body =
    match nablas with
    | [] -> (* short circuit *)
        apply_arrow (freshen_nameless_bindings ~support ~ts:0 foralls body) args
    | _ ->
        let n = List.length nablas in
        let (nabla_ids, nabla_tys) = List.split nablas in
        (* Add dummy nominals in case nabla bound variables aren't used *)
        let support =
          (fresh_nominals_by_list nabla_tys
             (List.map term_to_name (support @ used_nominals))) @
          support
        in
        support |> List.rev |> List.permute n
        |> List.find_all (fun nominals -> nabla_tys = List.map (tc []) nominals)
        |> List.find_some
          (fun nominals ->
             try_with_state ~fail:None
               (fun () ->
                  let support = List.minus support nominals in
                  let raised_body =
                    freshen_nameless_bindings ~support ~ts:0 foralls body
                  in
                  let alist = List.combine nabla_ids nominals in
                  let permuted_body =
                    replace_metaterm_vars alist raised_body
                  in
                  Some (apply_arrow permuted_body args)))
        |> (function
            | Some v -> v
            | None ->
                failwith "Failed to find instantiations for nabla quantified variables")
  in
  match term with
  | Binding(Forall, foralls, Binding(Nabla, nablas, body)) ->
      process_bindings foralls nablas body
  | Binding(Forall, foralls, body) ->
      process_bindings foralls [] body
  | Binding(Nabla, nablas, body) ->
      process_bindings [] nablas body
  | Arrow _ ->
      apply_arrow term args
  | term when args = [] ->
      (term, [])
  | _ ->
      [ "Structure of applied term must be a substructure of the following." ;
        "forall A1 ... Ai, nabla z1 ... zj, H1 -> ... -> Hk -> C" ]
      |> String.concat "\n" |> failwith

let rec ensure_unique_nominals lst =
  if not (List.is_unique lst) || not (List.for_all Term.is_nominal lst) then
    failwith "Invalid instantiation for nabla variable"

let take_from_binders binders withs =
  let withs' =
    List.find_all (fun (x,t) -> List.mem_assoc x binders) withs
  in
  let binders' = List.remove_all
    (fun (x, ty) -> List.mem_assoc x withs) binders
  in
    (binders', withs')

let rec instantiate_withs term withs =
  match term with
    | Binding(Forall, binders, body) ->
        let binders', withs' = take_from_binders binders withs in
        let binders_as_withs = List.map (fun (x, t) -> (x, const x t)) binders' in
        let body, used_nominals =
          instantiate_withs (replace_metaterm_vars (withs' @ binders_as_withs) body) withs
        in
          (normalize (forall binders' body), used_nominals)
    | Binding(Nabla, binders, body) ->
        let binders', withs' = take_from_binders binders withs in
        let binders_as_withs = List.map (fun (x, t) -> (x, const x t)) binders' in
        let nominals = List.map snd withs' in
        let support = metaterm_support body in
          ensure_unique_nominals nominals ;
          if List.exists (fun x -> List.mem x support) nominals then
            failwith "Invalid instantiation for nabla variable" ;
          let body, used_nominals =
            instantiate_withs (replace_metaterm_vars (withs' @ binders_as_withs) body) withs
          in
            (normalize (nabla binders' body), nominals @ used_nominals)
    | _ -> (term, [])

let apply_with term args withs =
  if args = [] && withs = [] then
    (term, [])
  else
    let term, used_nominals = instantiate_withs term withs in
      apply (normalize term) args ~used_nominals

(* Backchain *)

let backchain_arrow term goal =
  let obligations, head = decompose_arrow term in
  let () =
    match term_to_restriction head, term_to_restriction goal with
      | CoSmaller i, CoSmaller j when i = j -> ()
      | CoSmaller _, _ -> failwith "Coinductive restriction violated"
      | _, _ -> ()
  in
    begin match head, goal with
      | Obj(Async hobj, _), Obj(Async gobj, _) ->
          let hctx,hterm = Async.get hobj in
          let gctx,gterm = Async.get gobj in
          right_unify hterm gterm ;
          Context.backchain_reconcile hctx gctx
      | _, _ ->
          meta_right_unify head goal
    end ;
    obligations

let backchain ?(used_nominals=[]) term goal =
  let support = List.minus (metaterm_support goal) used_nominals in
    match term with
      | Binding(Forall, bindings, Binding(Nabla, nablas, body)) ->
          let n = List.length nablas in
          let (nabla_ids, nabla_tys) = List.split nablas in
            support |> List.rev |> List.permute n
              |> List.find_all
                  (fun nominals -> nabla_tys = List.map (tc []) nominals)
              |> List.find_some
                (fun nominals ->
                   try_with_state ~fail:None
                     (fun () ->
                        let support = List.minus support nominals in
                        let raised_body =
                          freshen_nameless_bindings ~support ~ts:0 bindings body
                        in
                        let alist = List.combine nabla_ids nominals in
                        let permuted_body =
                          replace_metaterm_vars alist raised_body
                        in
                          Some (backchain_arrow permuted_body goal)))
              |> (function
                    | Some v -> v
                    | None ->
                        failwith "Failed to find instantiations for nabla quantified variables")

      | Binding(Forall, bindings, body) ->
          backchain_arrow (freshen_nameless_bindings ~support ~ts:0 bindings body) goal

      | _ -> backchain_arrow term goal

(*
      | Arrow _ ->
          backchain_arrow term goal

      | _ -> failwith
          ("Structure of backchained term must be a " ^
             "substructure of the following.\n" ^
             "forall A1 ... Ai, nabla z1 ... zj, H1 -> ... -> Hk -> C")
*)


let backchain_with term withs goal =
  let term, used_nominals = instantiate_withs term withs in
    backchain term goal ~used_nominals

(* Permute nominals *)

let permute_nominals perm term =
  match perm with
    | h::t ->
        let perm' = t @ [h] in
        let alist =
          List.map2
            (fun src dest ->
               let v = term_to_var src in
                 (v.name, nominal_var (term_to_name dest) v.ty))
            perm perm'
        in
          replace_metaterm_vars alist term
    | _ -> assert false
