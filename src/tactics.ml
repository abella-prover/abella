open Term
open Lppterm
open Pprint

let is_imp t =
  match observe t with
    | App(t, _) -> eq t (const "=>")
    | _ -> false

let extract_imp t =
  match observe t with
    | App(t, [a; b]) -> (a, b)
    | _ -> failwith "Check is_imp before calling extract_imp"
          
let object_cut t1 t2 =
  match t1, t2 with
    | Obj(t1, _), Obj(t2, _) ->
        if is_imp t1 then
          let (a, b) = extract_imp t1 in
            if eq a t2 then
              obj b
            else
              failwith "Object cut applied to non-matching hypotheses"
        else
          failwith "First hypothesis to object cut must be an implication"
    | _ -> failwith "Object cut can only be used on objects"

let is_pi_abs t =
  match observe t with
    | App(t, [abs]) -> eq t (const "pi") &&
        begin match observe abs with
          | Lam(1, _) -> true
          | _ -> false
        end
    | _ -> false

let extract_pi_abs t =
  match observe t with
    | App(t, [abs]) -> abs
    | _ -> failwith "Check is_pi_abs before calling extract_pi_abs"
        
let object_inst t x =
  match t with
    | Obj(t, _) ->
        if is_pi_abs t then
          let abs = extract_pi_abs t in
            obj (Norm.deep_norm (app abs [x]))
        else
          failwith ("First hypothesis to object instantion must have the " ^
                      "form (pi x\\ ...)")
    | _ -> failwith ("Object instantiation expects an object as the first " ^
                       "argument")
        
let fresh_alist tag ts =
  List.map (fun x -> (x, var ~tag:tag x 0)) ts

let fresh_alist_wrt tag ts vars =
  let used = ref vars in
    (List.map (fun x ->
                let (fresh, curr_used) = fresh_wrt tag x !used in
                  used := curr_used ;
                  (x, fresh))
      ts)

let replace_vars alist t =
  let rec aux_term t =
    match observe t with
      | Var {name=name} when List.mem_assoc name alist ->
          List.assoc name alist
      | Var _
      | DB _ -> t
      | Lam(i, t) -> lambda i (aux_term t)
      | App(t, ts) -> app (aux_term t) (List.map aux_term ts)
      | Susp _ -> failwith "Susp found during replace_vars"
      | Ptr _ -> assert false
  in
  let rec aux_lppterm t =
    match t with
      | Obj(t, r) -> obj_r (aux_term t) r
      | Arrow(a, b) -> arrow (aux_lppterm a) (aux_lppterm b)
      | Forall _ -> failwith "Cannot replace vars inside forall"
  in
    aux_lppterm t

let extract_obj t =
  match t with
    | Obj(t, _) -> t
    | _ -> failwith "extract_obj called on non object"
        
let logic_var_names ts =
  List.map (fun v ->
              match observe v with
                | Var {name=name} -> name
                | _ -> failwith "logic_vars returned non-var")
    (logic_vars (List.map extract_obj ts))
                                                    
module Right =
  Unify.Make (struct
                let instantiatable = Logic
                let constant_like = Eigen
              end)
    
module Left =
  Unify.Make (struct
                let instantiatable = Eigen
                let constant_like = Logic
              end)

let check_restriction (n1, a1) (n2, a2) =
  if a1 && (n1 != n2 || not a2) then
    failwith "Restriction violated"
  else
    ()

let apply_forall stmt ts =
  match stmt with
    | Forall(bindings, body) ->
        let alist = fresh_alist Logic bindings in
        let fresh_body = replace_vars alist body in
          List.fold_left
            (fun stmt arg ->
               match stmt, arg with
                 | Arrow(Obj(left, r1), right), Obj(arg, r2) ->
                     check_restriction r1 r2 ;
                     begin try Right.pattern_unify left arg with
                       | Unify.Error _ ->
                           failwith "Unification failure"
                     end ;
                     right
                 | _ -> failwith "Too few implications in forall application")
            fresh_body
            ts
    | _ -> failwith "apply_forall can only be used on Forall(...) statements"

let right_object_unify t1 t2 =
  match t1, t2 with
    | Obj(t1, _), Obj(t2, _) -> Left.pattern_unify t1 t2
    | _ -> failwith "right_object_unify called on non-object"

let find_obj_vars ts =
  List.map (fun v -> v.name)
    (find_vars Eigen (List.map obj_to_term ts))

let is_capital str =
  match str.[0] with
    | 'A'..'Z' -> true
    | _ -> false

let uniq lst =
  List.fold_left
    (fun result x -> if List.mem x result then result else x::result)
    [] lst
    
let capital_var_names ts =
  uniq (List.filter is_capital
          (map_vars_list (fun v -> v.name)
             (List.map obj_to_term ts)))

let freshen_capital_vars tag ts used =
  let var_names = capital_var_names ts in
  let fresh_names = fresh_alist_wrt tag var_names used in
    List.map (replace_vars fresh_names) ts
    
let case term clauses used =
  let initial_state = save_state () in
    List.fold_right
      (fun (head, body) result ->
         match freshen_capital_vars Eigen (head::body) used with
           | [] -> assert false
           | fresh_head::fresh_body ->
               try
                 right_object_unify fresh_head term ;
                 let used_vars = find_obj_vars (fresh_head::fresh_body) in
                 let subst = get_subst initial_state in
                 let restore () = (restore_state initial_state ;
                                   apply_subst subst) in
                   restore_state initial_state ;
                   match term with
                     | Obj(_, (n, _)) when n > 0 ->
                         (restore, used_vars, List.map
                            (apply_active_restriction n) fresh_body)::result
                     | _ -> (restore, used_vars, fresh_body)::result
               with
                 | Unify.Error _ -> result)
      clauses []

let apply_restrictions active args stmt =
  let rec aux curr_arg args curr_ind stmt =
    match args with
      | [] -> stmt
      | (x::xs) ->
          match stmt with
            | Arrow(Obj(left, _), right) ->
                if x = curr_arg then
                  Arrow(obj_r left (curr_ind, active),
                        aux (curr_arg + 1) xs (curr_ind + 1) right)
                else
                  Arrow(obj left, aux (curr_arg + 1) (x::xs) curr_ind right)
            | _ -> failwith "Not enough implications in induction"
  in
    aux 1 args 1 stmt

let induction args stmt =
  match stmt with
    | Forall(bindings, body) ->
        let ih_body = apply_restrictions true args body in
        let goal_body = apply_restrictions false args body in
          (forall bindings ih_body, forall bindings goal_body)
    | _ -> failwith "Induction applied to non-forall statement"
