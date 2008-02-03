(****************************************************************************)
(* Copyright (C) 2007-2008 Gacek                                            *)
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

let is_question str =
  str.[0] = '?'
        
let question_var_names terms =
  terms
  |> map_vars_list (fun v -> v.name)
  |> List.find_all is_question
  |> List.unique

let is_capital str =
  match str.[0] with
    | 'A'..'Z' -> true
    | _ -> false
        
let capital_var_names terms =
  terms
  |> map_vars_list (fun v -> v.name)
  |> List.find_all is_capital
  |> List.unique

let free_capital_var_names metaterm =
  let aux_term = capital_var_names in
  let aux_obj obj = aux_term obj.context @ aux_term [obj.term] in
  let rec aux = function
    | Obj(obj, r) -> aux_obj obj
    | Arrow(a, b) -> aux a @ aux b
    | Binding(binder, bindings, body) ->
        List.remove_all (fun x -> List.mem x bindings) (aux body)
    | Or(a, b) -> aux a @ aux b
    | And(a, b) -> aux a @ aux b
    | Pred(p, r) -> aux_term [p]
  in
    List.unique (aux metaterm)

let alist_to_used (_, t) = term_to_pair t

let freshen_clause ~used ?(support=[]) head body =
  let var_names = capital_var_names (head::body) in
  let fresh_names = fresh_alist ~tag:Eigen ~used var_names in
  let raised_names = raise_alist ~support fresh_names in
    (List.map alist_to_used fresh_names @ used,
     replace_term_vars raised_names head,
     List.map (replace_term_vars raised_names) body)

let freshen_def ~used ?(support=[]) head body =
  let var_names = capital_var_names [head] in
  let fresh_names = fresh_alist ~tag:Eigen ~used var_names in
  let raised_names = raise_alist ~support fresh_names in
    (List.map alist_to_used fresh_names @ used,
     replace_term_vars raised_names head,
     List.map (replace_metaterm_vars raised_names) body)

let term_vars_alist tag terms =
  List.map term_to_pair (find_var_refs tag terms)
    
let metaterm_vars_alist tag metaterms =
  term_vars_alist tag (List.flatten_map collect_terms metaterms)
      
(* Freshening for Logic variables uses anonymous names *)
      
let fresh_nameless_alist ~support ids =
  List.map (fun x -> (x, app (fresh ~tag:Logic 0) support)) ids
      
let freshen_nameless_clause ?(support=[]) head body =
  let var_names = capital_var_names (head::body) in
  let fresh_names = fresh_nameless_alist ~support var_names in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = List.map (replace_term_vars fresh_names) body in
    (fresh_head, fresh_body)

let freshen_nameless_def ?(support=[]) head body =
  let var_names = capital_var_names [head] in
  let fresh_names = fresh_nameless_alist ~support var_names in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = List.map (replace_metaterm_vars fresh_names) body in
    (fresh_head, fresh_body)

let freshen_nameless_bindings ?(support=[]) bindings term =
  replace_metaterm_vars (fresh_nameless_alist ~support bindings) term

(* Object level cut *)

(* obj1 = L2, A |- C
   obj2 = L1 |- A
   result = L2, L1 |- C *)
let object_cut obj1 obj2 =
  if Context.mem obj2.term obj1.context then
    let ctx =
      obj1.context
      |> Context.remove obj2.term
      |> Context.union obj2.context
      |> Context.normalize 
    in
      Obj(context_obj ctx obj1.term, Irrelevant)
  else
    failwith "Needless use of cut"

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

let stateless_case_to_case case =
  { bind_state = get_bind_state () ;
    new_vars = case.stateless_new_vars ;
    new_hyps = case.stateless_new_hyps }

let rec recursive_metaterm_case ~used term =
  match term with
    | And(left, right) ->
        let {stateless_new_vars = vars_left ;
             stateless_new_hyps = hyps_left } =
          recursive_metaterm_case ~used left
        in
        let right_case =
          recursive_metaterm_case ~used:(vars_left @ used) right
        in
          { stateless_new_vars = vars_left @ right_case.stateless_new_vars ;
            stateless_new_hyps = hyps_left @ right_case.stateless_new_hyps }
    | Binding(Exists, ids, body) ->
        let fresh_ids = fresh_alist ~used ~tag:Eigen ids in
        let support = metaterm_support term in
        let raised_ids = raise_alist ~support fresh_ids in
        let fresh_body = replace_metaterm_vars raised_ids body in
        let new_vars = List.map alist_to_used fresh_ids in
        let nested_case =
          recursive_metaterm_case ~used:(new_vars @ used) fresh_body
        in
          {nested_case with
             stateless_new_vars = new_vars @ nested_case.stateless_new_vars}
    | Binding(Nabla, [id], body) ->
        let nominal = fresh_nominal body in
        let fresh_body = replace_metaterm_vars [(id, nominal)] body in
          recursive_metaterm_case ~used fresh_body
    | _ -> {stateless_new_vars = [] ; stateless_new_hyps = [term]}

let rec or_to_list term =
  match term with
    | Or(left, right) -> (or_to_list left) @ (or_to_list right)
    | _ -> [term]

let predicate_wrapper r t =
  let rec aux t =
    match t with
      | Pred(p, _) -> Pred(p, reduce_restriction r)
      | Binding(binding, ids, body) -> Binding(binding, ids, aux body)
      | Or(t1, t2) -> Or(aux t1, aux t2)
      | And(t1, t2) -> And(aux t1, aux t2)
      | Arrow(t1, t2) -> Arrow(t1, aux t2)
      | Obj _ -> t
  in
    aux t
    
let lift_all ~used nominals =
  List.fold_left
    (fun used (id, term) ->
       if is_free term then
         let new_term, new_used = fresh_wrt Eigen id used in
           bind term (app new_term nominals) ;
           new_used
       else
         used)
    used
    used

let case ~used ~clauses ~defs ~global_support term =

  let support = metaterm_support term in
  let initial_bind_state = get_bind_state () in
  
  let def_case ~wrapper term =
    let make_case ~support ~used (head, body) term =
      let used, head, body =
        freshen_def ~support ~used head body
      in
        if try_left_unify ~used head term then
          let bind_state = get_bind_state () in
            (* Names created perhaps by raising *)
          let newly_used =
            used |> List.find_all (fun (_, t) -> is_free t) |> List.unique
          in
            (* Names created perhaps by unificiation *)
          let newly_used_head = term_vars_alist Eigen [head] in
          let newly_used_body = metaterm_vars_alist Eigen body in
            [{ bind_state = bind_state ;
               new_vars = newly_used @ newly_used_head @ newly_used_body ;
               new_hyps = List.map wrapper body }]
        else
          []
    in
      defs |> List.flatten_map
          (function
             | Pred(head, _), body ->
                 set_bind_state initial_bind_state ;
                 make_case ~support ~used (head, body) term
             | Binding(Nabla, [id], Pred(head, _)), body ->
                 let raised_result =
                   set_bind_state initial_bind_state ;
                   (* should be fresh with respect to global_support *)
                   let n = fresh_nominal (pred (app head global_support)) in
                   let alist = [(id, n)] in
                   let used = lift_all ~used [n] in
                   let head = replace_term_vars alist head in
                   let body = List.map (replace_metaterm_vars alist) body in
                     make_case ~support ~used (head, body) term
                 in
                 let permuted_results =
                   support |> List.flatten_map
                       (fun dest ->
                          set_bind_state initial_bind_state ;
                          let alist = [(id, dest)] in
                          let support = List.remove dest support in
                          let head = replace_term_vars alist head in
                          let body =
                            List.map (replace_metaterm_vars alist) body in
                            make_case ~support ~used (head, body) term)
                 in
                   raised_result @ permuted_results
             | _ -> failwith "Bad head in definition")
  in
          
  let clause_case ~wrapper term =
    clauses |> List.filter_map
        (fun (head, body) ->
           set_bind_state initial_bind_state ;           
           let used, fresh_head, fresh_body =
             freshen_clause ~support ~used head body
           in
             if try_left_unify ~used fresh_head term then
               let new_vars = term_vars_alist Eigen (fresh_head::fresh_body) in
               let bind_state = get_bind_state () in
               let wrapped_body = List.map wrapper fresh_body in
                 set_bind_state initial_bind_state ;
                 Some { bind_state = bind_state ;
                        new_vars = new_vars ;
                        new_hyps = wrapped_body }
             else
               None)
  in
    
  let obj_case obj r =
    let wrapper t = Obj(context_obj obj.context t, reduce_restriction r) in
    let clause_cases = clause_case ~wrapper obj.term in
      if Context.is_empty obj.context then
        clause_cases
      else
        let member_case =
          { bind_state = get_bind_state () ;
            new_vars = [] ;
            new_hyps = [obj_to_member obj] }
        in
          member_case :: clause_cases
  in
    
    match term with
      | Obj(obj, r) -> obj_case obj r
      | Pred(p, r) -> def_case ~wrapper:(predicate_wrapper r) p
      | Or _ -> List.map stateless_case_to_case
          (List.map (recursive_metaterm_case ~used) (or_to_list term))
      | And _
      | Binding(Exists, _, _)
      | Binding(Nabla, _, _) ->
          [stateless_case_to_case (recursive_metaterm_case ~used term)]
      | _ -> invalid_metaterm_arg term
          


(* Induction *)

let rec apply_restriction_at res stmt arg =
  match stmt with
    | Arrow(left, right) ->
        if arg = 1 then
          Arrow(apply_restriction res left, right)
        else
          Arrow(left, apply_restriction_at res right (arg-1))
    | _ -> failwith "Not enough implications in induction"

let induction ind_arg ind_num stmt =
  let rec aux stmt =
    match stmt with
      | Binding(Forall, bindings, body) ->
          let (ih, goal) = aux body in
            (forall bindings ih, forall bindings goal)
      | Binding(Nabla, bindings, body) ->
          let (ih, goal) = aux body in
            (nabla bindings ih, nabla bindings goal)
      | term ->
          let ih = apply_restriction_at (Smaller ind_num) term ind_arg in
          let goal = apply_restriction_at (Equal ind_num) term ind_arg in
            (ih, goal)
  in
    aux stmt

(* Search *)

let derivable goal hyp =
  try_right_unify goal.term hyp.term &&
    Context.subcontext hyp.context goal.context

let is_false t =
  match t with
    | Pred(p, _) ->
        begin match observe p with
          | Var {name=f} when f = "false" -> true
          | _ -> false
        end
    | _ -> false

let search ~depth:n ~hyps ~clauses ~defs goal =
  
  let rec term_aux n context goal =
    clauses |> List.exists
      (fun (head, body) ->
         try_with_state
           (fun () ->
              let support = term_support goal in
              let fresh_head, fresh_body =
                freshen_nameless_clause ~support head body
              in
                right_unify fresh_head goal ;
                List.for_all
                  (fun t -> obj_aux (n-1) {context=context; term=t})
                  fresh_body))
      
  and obj_aux n goal =
    if hyps |> filter_objs |> List.exists (derivable goal) then
      true
    else if Context.exists (try_right_unify goal.term) goal.context then
      true
    else if n = 0 then
      false
    else if is_imp goal.term then
      obj_aux (n-1) (move_imp_to_context goal)
    else if is_pi_abs goal.term then
      obj_aux (n-1) (replace_pi_abs_with_nominal goal)
    else
      let context_search () =
        not (Context.is_empty goal.context) &&
          metaterm_aux (n-1) (obj_to_member goal)
      in
      let backchain () =
        term_aux n goal.context goal.term
      in
        context_search () || backchain ()
        
  and metaterm_aux n goal =
    if hyps |> List.exists (try_meta_right_permute_unify goal) then
      true
    else
      let support = metaterm_support goal in
      match goal with
        | Or(left, right) -> metaterm_aux n left || metaterm_aux n right
        | And(left, right) -> metaterm_aux n left && metaterm_aux n right
        | Binding(Exists, bindings, body) ->
            let term = freshen_nameless_bindings ~support bindings body in
              metaterm_aux n term
        | Binding(Nabla, [id], body) ->
            let nominal = fresh_nominal body in
            let body = replace_metaterm_vars [(id, nominal)] body in
              metaterm_aux n body
        | Obj(obj, _) -> obj_aux n obj
        | Pred(p, _) ->
            List.exists (try_right_unify p) (filter_preds hyps) ||
              meta_aux n p
        | _ -> false

  and meta_aux n goal =
    let support = term_support goal in
    if n = 0 then false else
      defs |> List.exists
          (fun (head, body) ->
             try_with_state
               (fun () ->
                  match head with
                    | Pred(head, _) ->
                        let head, body =
                          freshen_nameless_def ~support head body
                        in
                          right_unify head goal ;
                          List.for_all (metaterm_aux (n-1))
                            (List.map normalize body)
                            
                    | Binding(Nabla, [id], Pred(head, _)) ->
                          support |> List.exists
                            (fun dest ->
                               try_with_state
                                 (fun () ->
                                    let support = List.remove dest support in
                                    let head = replace_term_vars
                                      [(id, dest)] head in
                                    let head, body =
                                      freshen_nameless_def
                                        ~support head body
                                    in
                                      right_unify head goal ;
                                      List.for_all (metaterm_aux (n-1))
                                        (List.map normalize body)))
                    | _ -> failwith "Bad head in definition"))
  in
    metaterm_aux n goal

      
(* Apply one statement to a list of other statements *)

let check_restrictions formal actual =
  List.iter2 (fun fr ar -> match fr, ar with
                | Smaller i, Smaller j when i = j -> ()
                | Equal i, Smaller j when i = j -> ()
                | Equal i, Equal j when i = j -> ()
                | Irrelevant, _ -> ()
                | _ -> failwith "Restriction violated")
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

let apply term args =
  let support =
    args
    |> List.flatten_map (Option.map_default metaterm_support [])
    |> List.unique
  in
  let rec aux term =
    match term with
      | Binding(Forall, bindings, Binding(Nabla, [var], body)) ->
          (* TODO: What about nested nablas, they should be distinct *)
          let state = get_bind_state () in
            support |> List.find_some
                (fun dest ->
                   try
                     let support = List.remove dest support in
                     let raised_body =
                       freshen_nameless_bindings ~support bindings body
                     in
                     let permuted_body =
                       replace_metaterm_vars [(var, dest)] raised_body
                     in
                       Some (aux permuted_body)
                   with
                   | UnifyFailure _ | UnifyError _ ->
                       set_bind_state state ; None)
      | Binding(Forall, bindings, body) ->
          aux (freshen_nameless_bindings ~support bindings body)
      | Arrow _ ->
          let formal = map_args term_to_restriction term in
          let actual = List.map some_term_to_restriction args in
          let context_pairs = ref [] in
          let obligations = ref [] in
            check_restrictions formal actual ;
            let result =
              List.fold_left
                (fun term arg ->
                   match term, arg with
                     | Arrow(Obj(left, _), right), Some Obj(arg, _) ->
                         context_pairs :=
                           (left.context, arg.context)::!context_pairs ;
                         right_unify left.term arg.term ;
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
      | _ -> failwith "Attempting to apply malformed term"

  in
    aux term


(* Unfold the current goal *)
let find_as f list =
  let rec aux list =
    match list with
      | x::xs ->
          begin match f x with
            | Some y -> y
            | None -> aux xs
          end
      | _ -> raise Not_found
  in
    aux list
      
let unfold ~used ~defs term =
  let support = metaterm_support term in
    match term with
      | Pred(term, _) ->
          defs |> find_as
              (fun (head, body) ->
                 try
                   let used, head, body =
                     match head with
                       | Pred(p, _) -> used, p, body
                       | _ -> failwith "Not yet implemented"
                   in
                   let head, body =
                     freshen_nameless_def ~support head body
                   in
                     if try_right_unify ~used head term then
                       Some body
                     else
                       None
                 with Failure("Not yet implemented") -> None)
      | _ -> failwith "Can only unfold predicates"
