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
open Debug

(* Variable naming utilities *)

let alist_to_used (_, t) = term_to_pair t

let freshen_clause ~used ?(support=[]) head body =
  let tids = capital_tids (head::body) in
  let (alist, vars) = fresh_raised_alist ~tag:Eigen ~used ~support tids in
    (List.map term_to_pair vars @ used,
     replace_term_vars alist head,
     List.map (replace_term_vars alist) body)

let freshen_def ~used ?(support=[]) head body =
  let tids = capital_tids [head] in
  let (alist, vars) = fresh_raised_alist ~tag:Eigen ~used ~support tids in
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

let freshen_nameless_clause ?(support=[]) ~ts head body =
  let tids = capital_tids (head::body) in
  let fresh_names = fresh_nameless_alist ~support ~tag:Logic ~ts tids in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = List.map (replace_term_vars fresh_names) body in
    (fresh_head, fresh_body)

let freshen_nameless_def ?(support=[]) ~ts head body =
  let tids = capital_tids [head] in
  let fresh_names = fresh_nameless_alist ~support ~tag:Logic ~ts tids in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = replace_metaterm_vars fresh_names body in
    (fresh_head, fresh_body)

let freshen_nameless_bindings ~support ~ts bindings term =
  let alist = fresh_nameless_alist ~support ~tag:Logic ~ts bindings in
    replace_metaterm_vars alist term

(* Object level cut *)

(* ctx1 |- t1  ==  L, ..., A |- C
   ctx2 |- t2  ==  L, ...    |- A
   result      ==  L, ...    |- C *)
let object_cut (ctx1, t1) (ctx2, t2) =
  if Context.mem t2 ctx1 then
    let rctx =
      ctx1
      |> Context.remove t2
      |> Context.union ctx2
      |> Context.normalize
    in
      if Context.wellformed rctx then
        (rctx, t1)
      else
        failwith "Cannot merge contexts"
  else
    failwith "Needless use of cut"


(* Search cut *)

let search_cut ~search_goal ctx =
  (* Process the context from head to tail looking for goals to remove *)
  let rec aux left right =
    match right with
      | d::ds ->
          if search_goal (Obj(Seq(left @ ds, d), Irrelevant)) then
            aux left ds
          else
            aux (d::left) ds
      | [] -> left
  in
    aux [] (List.rev ctx)

(* Object level instantiation *)

(* inst t1 with n = t2 *)
let object_inst t1 n t2 =
  if List.mem n (List.map term_to_name (metaterm_support t1)) then
    match t1 with
      | Obj(obj, r) ->
          let r =
            match tc [] t2 with
              | Ty(_, "o") -> Irrelevant
              | _ -> r
          in
            Obj(map_obj (replace_term_vars ~tag:Nominal [(n, t2)]) obj, r)
      | _ -> assert false
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

(* This handles asyncrony on the left *)
let rec recursive_metaterm_case ~used term =
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
        begin match recursive_metaterm_case ~used left with
          | None -> None
          | Some {stateless_new_vars = vars_left ;
                  stateless_new_hyps = hyps_left } ->
              match recursive_metaterm_case ~used:(vars_left @ used) right with
                | None -> None
                | Some {stateless_new_vars = vars_right ;
                        stateless_new_hyps = hyps_right } ->
                    Some { stateless_new_vars = vars_left @ vars_right ;
                           stateless_new_hyps = hyps_left @ hyps_right }
        end
    | Binding(Exists, tids, body) ->
        let support = metaterm_support term in
        let (alist, vars) = fresh_raised_alist ~tag:Eigen ~used ~support tids in
        let fresh_body = replace_metaterm_vars alist body in
        let new_vars = List.map term_to_pair vars in
        let nested =
          recursive_metaterm_case ~used:(new_vars @ used) fresh_body
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
          recursive_metaterm_case ~used fresh_body
    | _ -> Some {stateless_new_vars = [] ; stateless_new_hyps = [term]}

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

let lift_all ~used nominals =
  let ntys = List.map (tc []) nominals in
    used |> List.iter
        (fun (id, term) ->
           if is_free term then
             let v = term_to_var term in
             let new_term = var Eigen id v.ts (tyarrow ntys v.ty) in
               bind term (app new_term nominals))

let case ~used ~clauses ~mutual ~defs ~global_support term =

  let support = metaterm_support term in

  let def_case ~wrapper term =
    let make_case ~support ~used (head, body) term =
      let fresh_used, head, body =
        freshen_def ~support ~used head body
      in
        match try_left_unify_cpairs ~used:(fresh_used @ used) head term with
          | Some cpairs ->
              (* Names created perhaps by unificiation *)
              let used_head = term_vars_alist Eigen [head; term] in
              let used_body = metaterm_vars_alist Eigen body in
              let used = List.unique (used_head @ used_body @ used) in
                begin match recursive_metaterm_case ~used body with
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
                                     let () = lift_all ~used nominals in
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

  let clause_case ~wrapper term =
    if has_eigen_head term then
      failwith "Cannot perform case-analysis on flexible head" ;
    clauses |> List.filter_map
        (unwind_state
           (fun (head, body) ->
              let fresh_used, fresh_head, fresh_body =
                freshen_clause ~support ~used head body
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
  in

  let obj_case obj r =
    match obj with
      | Seq(ctx, g) ->
          let wrapper t =
            Obj(Seq(ctx, t), reduce_inductive_restriction r)
          in
          let clause_cases = clause_case ~wrapper g in
            if Context.is_empty ctx then
              clause_cases
            else
              let bc_case =
                match
                  recursive_metaterm_case ~used
                    (seq_to_bc ctx g (reduce_inductive_restriction r))
                with
                  | None -> assert false
                  | Some case ->
                      { bind_state = get_bind_state () ;
                        new_vars = case.stateless_new_vars ;
                        new_hyps = case.stateless_new_hyps }
              in
                bc_case :: clause_cases

      | Bc(ctx, c, a) ->
          let ntys = List.map (tc []) support in
          let rec decompose ~used head body =
            match clause_view head with
              | Imp(left, right) ->
                  decompose ~used right (left::body)
              | Pi(ty, abs) ->
                  let x, used =
                    fresh_wrt ~ts:0 Eigen "X" (tyarrow ntys ty) used
                  in
                  let rx = app x support in
                    decompose ~used (app abs [rx]) body
              | Raw _ ->
                  if has_eigen_head head then
                    failwith "Cannot perform case-analysis on flexible clause" ;
                  (used, head, body)
          in
          let used, head, body = decompose ~used c [] in
            unwind_state
              (fun () ->
                 match try_left_unify_cpairs ~used head a with
                   | Some cpairs ->
                       let new_vars =
                         term_vars_alist Eigen (head::a::body)
                       in
                       let wrapped_body =
                         List.map
                           (fun t -> Obj(Seq(ctx, t), reduce_inductive_restriction r))
                           body
                       in
                         [{ bind_state = get_bind_state () ;
                            new_vars = new_vars ;
                            new_hyps = cpairs_to_eqs cpairs @ wrapped_body}]
                   | None -> []
              )
              ()
  in

    match term with
      | Obj(obj, r) -> obj_case obj r
      | Pred(_, CoSmaller _) -> failwith "Cannot case analyze hypothesis\
                                          \ with coinductive restriction"
      | Pred(p, r) ->
          def_case ~wrapper:(predicate_wrapper r mutual) p
      | Or _ ->
          List.filter_map
            (unwind_state
               (fun g ->
                  match recursive_metaterm_case ~used g with
                    | None -> None
                    | Some c -> Some (stateless_case_to_case c)))
            (or_to_list term)
      | Eq _
      | And _
      | Binding(Exists, _, _)
      | Binding(Nabla, _, _) ->
          Option.map_default (fun sc -> [stateless_case_to_case sc]) []
            (recursive_metaterm_case ~used term)
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
          else
            t
      | Binding(binding, ids, body) -> Binding(binding, ids, aux body)
      | Or(t1, t2) -> Or(aux t1, aux t2)
      | And(t1, t2) -> And(aux t1, aux t2)
      | Arrow(t1, t2) -> Arrow(t1, aux t2)
  in
    aux t

let unfold_defs ~mdefs ~ts goal r =
  let p = term_head_name goal in
  let (mutual, defs) = mdefs in
  let support = term_support goal in
  let wrapper = coinductive_wrapper r mutual in
  let unfold_def tids head body i =
    let (ids, tys) = List.split tids in
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

let unfold ~mdefs goal =
  match goal with
    | Pred(_, Smaller _) | Pred(_, Equal _) ->
        failwith "Cannot unfold inductively restricted predicate"
    | Pred(goal, r) ->
        (* Find the first body without lingering conflict pairs *)
        let rec select_non_cpair list =
          match list with
            | (state, [], body, _)::_ -> set_bind_state state; body
            | _::rest -> select_non_cpair rest
            | [] -> failwith "No matching definitions"
        in
          select_non_cpair (unfold_defs ~mdefs ~ts:0 goal r)
    | _ -> failwith "Can only unfold defined predicates"


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
  | WBc of witness list

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
          id ^ "[" ^ (string_of_int n) ^ "]" ^ aux_list ws
    | WBc(ws) ->
          "bc" ^ aux_list ws

  and aux_list = function
    | [] -> ""
    | ws -> "(" ^ String.concat ", " (List.map aux ws) ^ ")"
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

let try_unify_cpairs cpairs =
  List.for_all (curry try_right_unify) cpairs

let assoc_mdefs name alldefs =
  try
    List.find (fun (ids, defs) -> List.mem name ids) alldefs
  with Not_found ->
    ([], [])

let alist_to_ids alist =
  List.map term_to_string (List.map snd alist)

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

  let rec clause_aux n hyps context goal r ts ~sc =
    let support = term_support goal in
    let freshen_clause = curry (freshen_nameless_clause ~support ~ts) in
    let p = term_head_name goal in
    let wrap body = List.map (fun b -> Seq(context, b)) body in
      clauses
      |> List.find_all (fun (h, _) -> term_head_name h = p)
      |> List.map freshen_clause
      |> List.number
      |> List.iter
          (unwind_state
             (fun (i, (head, body)) ->
                match try_right_unify_cpairs head goal with
                  | None ->
                      ()
                  | Some cpairs ->
                      obj_aux_conj (n-1) (wrap body) r ts
                        ~sc:(fun ws -> if try_unify_cpairs cpairs then
                               sc (WUnfold(p, i, ws)))))

  and obj_aux n hyps goal r ts ~sc =
    match normalize_obj goal with
      | Seq(ctx, g) ->
          (* Check hyps for derivability *)
          hyps
          |> List.filter_map
              (fun (id, h) ->
                 match h with
                   | Obj(Seq(hctx, hg), _) -> Some (id, hctx, hg)
                   | _ -> None)
          |> List.iter
              (unwind_state
                 (fun (id, hctx, hg) ->
                    if derivable (ctx, [g]) (hctx, [hg]) then sc (WHyp id))) ;

          begin match r with
            | Smaller _ | Equal _ -> ()
            | _ ->
                (* Check context *)
                if not (Context.is_empty ctx) then
                  metaterm_aux n hyps
                    (seq_to_bc ctx g (reduce_inductive_restriction r))
                    ts ~sc:(fun w -> sc (WUnfold(term_head_name g, 0, [w]))) ;

                (* Backchain *)
                if n > 0 then clause_aux n hyps ctx g r ts ~sc
          end

     | Bc(ctx, d, a) ->
         (* Check hyps for derivability *)
         hyps
         |> List.filter_map
             (fun (id, h) ->
                match h with
                  | Obj(Bc(hctx, hd, ha), _) -> Some (id, hctx, hd, ha)
                  | _ -> None)
         |> List.iter
             (unwind_state
                (fun (id, hctx, hd, ha) ->
                   if derivable (ctx, [d; a]) (hctx, [hd; ha]) then
                     sc (WHyp id))) ;

         begin match r with
           | Smaller _ | Equal _ -> ()
           | _ ->
               (* Backchain *)
               let support = obj_support goal in
               let ntys = List.map (tc []) support in
               let rec decompose head body =
                 match clause_view head with
                   | Imp(left, right) ->
                       decompose right (left::body)
                   | Pi(ty, abs) ->
                       let x = fresh ts (tyarrow ntys ty) in
                       let rx = app x support in
                         decompose (app abs [rx]) body
                   | Raw _ ->
                       (head, body)
               in
               let head, body = decompose d [] in
                 match try_right_unify_cpairs head a with
                   | None -> ()
                   | Some cpairs ->
                       let wrapped_body = List.map (fun b -> Seq(ctx, b)) body in
                         obj_aux_conj (n-1) wrapped_body
                           (reduce_inductive_restriction r) ts
                           ~sc:(fun ws -> if try_unify_cpairs cpairs then
                                  sc (WBc ws))
         end

  and obj_aux_conj n goals r ts ~sc =
    match goals with
      | [] -> sc []
      | g::gs -> obj_aux n hyps g r ts
          ~sc:(fun w -> obj_aux_conj n gs r ts ~sc:(fun ws -> sc (w::ws)))

  and metaterm_aux n hyps goal ts ~sc =
    hyps |> List.iter
        (unwind_state
           (fun (id, hyp) ->
              if (match hyp, goal with
                    | Pred(_, CoSmaller i), Pred(_, CoSmaller j) when i = j -> true
                    | Pred(_, CoSmaller _), _ -> false

                    | Pred(_, Smaller i), Pred(_, Smaller j)
                    | Pred(_, Smaller i), Pred(_, Equal j)
                    | Pred(_, Equal i), Pred(_, Equal j) when i = j -> true

                    | _, Pred(_, Smaller _) -> false
                    | _, Pred(_, Equal _) -> false

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
      | Obj(obj, r) -> obj_aux n hyps obj r ts ~sc
      | Pred(_, Smaller _) | Pred(_, Equal _) -> ()
      | Pred(p, r) -> if n > 0 then def_aux n hyps p r ts ~sc

  and def_aux n hyps goal r ts ~sc =
    let p = term_head_name goal in
    let mdefs = assoc_mdefs p alldefs in
      unwind_state
        (fun () ->
           unfold_defs ~mdefs ~ts goal r |> List.iter
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
           | Arrow(Obj(Seq(lctx, lg), _), right), Some Obj(Seq(actx, ag), _) ->
               context_pairs := (lctx, actx)::!context_pairs ;
               debug (Printf.sprintf "Trying to unify %s and %s."
                        (term_to_string lg) (term_to_string ag)) ;
               right_unify lg ag ;
               right
           | Arrow(left, right), Some arg ->
               debug (Printf.sprintf "Trying to unify %s and %s."
                        (metaterm_to_string left) (metaterm_to_string arg)) ;
               meta_right_unify left arg ;
               right
           | Arrow(left, right), None ->
               obligations := left::!obligations ;
               right
           | _ -> failwith "Too few implications in application")
      term
      args
  in
    debug "Trying to reconcile specification logic contexts." ;
    Context.reconcile !context_pairs ;
    (normalize result, !obligations)

let apply ?(used_nominals=[]) term args =
  let support =
    args
    |> List.flatten_map (Option.map_default metaterm_support [])
    |> List.unique
    |> fun s -> List.minus s used_nominals
  in
    match term with
      | Binding(Forall, bindings, Binding(Nabla, nablas, body)) ->
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
                          freshen_nameless_bindings ~support ~ts:0 bindings body
                        in
                        let alist = List.combine nabla_ids nominals in
                        let permuted_body =
                          replace_metaterm_vars alist raised_body
                        in
                          debug (Printf.sprintf "Trying apply with %s."
                                   (String.concat ", "
                                      (List.map
                                         (fun (x,n) ->
                                            x ^ " = " ^ (term_to_string n))
                                         alist))) ;
                          Some (apply_arrow permuted_body args)))
              |> (function
                    | Some v -> v
                    | None ->
                        failwith "Failed to find instantiations for nabla quantified variables")

      | Binding(Forall, bindings, body) ->
          apply_arrow (freshen_nameless_bindings ~support ~ts:0 bindings body) args

      | Arrow _ ->
          apply_arrow term args

      | term when List.length args = 0 -> (term, [])

      | _ -> failwith
          ("Structure of applied term must be a " ^
             "substructure of the following.\n" ^
             "forall A1 ... Ai, nabla z1 ... zj, H1 -> ... -> Hk -> C")

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
        let body, used_nominals =
          instantiate_withs (replace_metaterm_vars withs' body) withs
        in
          (forall binders' body, used_nominals)
    | Binding(Nabla, binders, body) ->
        let binders', withs' = take_from_binders binders withs in
        let nominals = List.map snd withs' in
        let support = metaterm_support body in
          ensure_unique_nominals nominals ;
          if List.exists (fun x -> List.mem x support) nominals then
            failwith "Invalid instantiation for nabla variable" ;
          let body, used_nominals =
            instantiate_withs (replace_metaterm_vars withs' body) withs
          in
            (nabla binders' body, nominals @ used_nominals)
    | _ -> (term, [])

let apply_with term args withs =
  let term, used_nominals = instantiate_withs term withs in
    apply (normalize term) args ~used_nominals

(* Backchain *)

let check_restrictions formal actual =
  List.iter2 (fun fr ar -> match fr, ar with
                | Smaller i, Smaller j when i = j -> ()
                | Equal i, Smaller j when i = j -> ()
                | Equal i, Equal j when i = j -> ()
                | Irrelevant, _ -> ()
                | _ -> failwith "Inductive restriction violated")
    formal actual

let backchain_arrow term goal =
  let obligations, head = decompose_arrow term in
  let () =
    match term_to_restriction head, term_to_restriction goal with
      | CoSmaller i, CoSmaller j when i = j -> ()
      | CoSmaller _, _ -> failwith "Coinductive restriction violated"
      | _, _ -> ()
  in
    begin match head, goal with
      | Obj(Seq(hctx, hg), _), Obj(Seq(gctx, gg), _) ->
          right_unify hg gg ;
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

      | Arrow _ ->
          backchain_arrow term goal

      | _ -> failwith
          ("Structure of backchained term must be a " ^
             "substructure of the following.\n" ^
             "forall A1 ... Ai, nabla z1 ... zj, H1 -> ... -> Hk -> C")


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
