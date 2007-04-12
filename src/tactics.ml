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
  let t1 = obj_to_term t1 in
  let t2 = obj_to_term t2 in 
  let (a, b) = extract_imp t1 in
    if eq a t2 then
      obj b
    else
      failwith "Object cut applied to non-matching hypotheses"
        
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
  let t = obj_to_term t in
  let abs = extract_pi_abs t in
    obj (Norm.deep_norm (app abs [x]))
        
let fresh_alist tag ts =
  List.map (fun x -> (x, var ~tag:tag x 0)) ts

let fresh_alist_wrt tag ts vars =
  let used = ref vars in
    (List.map (fun x ->
                let (fresh, curr_used) = fresh_wrt tag x !used in
                  used := curr_used ;
                  (x, fresh))
      ts)

let replace_term_vars alist t =
  let rec aux t =
    match observe t with
        | Var {name=name} when List.mem_assoc name alist ->
            List.assoc name alist
        | Var _
        | DB _ -> t
        | Lam(i, t) -> lambda i (aux t)
        | App(t, ts) -> app (aux t) (List.map aux ts)
        | Susp _ -> failwith "Susp found during replace_vars"
        | Ptr _ -> assert false
  in
    aux t

let replace_lppterm_vars alist t =
  let rec aux t =
    match t with
      | Obj(t, r) -> obj_r (replace_term_vars alist t) r
      | Arrow(a, b) -> arrow (aux a) (aux b)
      | Forall _ -> failwith "Cannot replace vars inside forall"
      | Or(a, b) -> lpp_or (aux a) (aux b)
  in
    aux t
        
let logic_var_names ts =
  List.map (fun v ->
              match observe v with
                | Var {name=name} -> name
                | _ -> failwith "logic_vars returned non-var")
    (logic_vars (List.map obj_to_term ts))
                                                    
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

let check_restrictions formal actual =
  List.iter2 (fun fr ar -> match fr, ar with
                | Smaller, Equal
                | Smaller, Irrelevant ->
                    failwith "Restriction violated"
                | _ -> ())
    formal actual

let obj_to_restriction t =
  match t with
    | Obj(_, r) -> r
    | _ -> failwith "obj_to_restriction called on non-object"

let rec map_args f t =
  match t with
    | Arrow(left, right) ->
        (f left) :: (map_args f right)
    | Obj _ -> []
    | Or(left, right) ->
        List.append (map_args f left) (map_args f right)
    | _ -> invalid_lppterm_arg t

let apply_forall stmt ts =
  match stmt with
    | Forall(bindings, body) ->
        let alist = fresh_alist Logic bindings in
        let fresh_body = replace_lppterm_vars alist body in
        let formal = map_args obj_to_restriction fresh_body in
        let actual = List.map obj_to_restriction ts in
          check_restrictions formal actual ;
          List.fold_left
            (fun stmt arg ->
               match stmt, arg with
                 | Arrow(Obj(left, _), right), Obj(arg, _) ->
                     begin try Right.pattern_unify left arg with
                       | Unify.Error _ ->
                           failwith "Unification failure"
                     end ;
                     right
                 | _ -> failwith "Too few implications in forall application")
            fresh_body
            ts
    | _ -> failwith "apply_forall can only be used on Forall(...) statements"

let left_object_unify t1 t2 =
  let t1 = obj_to_term t1 in
  let t2 = obj_to_term t2 in
    Left.pattern_unify t1 t2

let right_object_unify t1 t2 =
  let t1 = obj_to_term t1 in
  let t2 = obj_to_term t2 in
    Right.pattern_unify t1 t2

let try_with_state f =
  let state = save_state () in
    try
      f ()
    with
      | _ -> restore_state state ; false

let try_right_object_unify t1 t2 =
  try_with_state
    (fun () ->
       right_object_unify t1 t2 ;
       true)
      
let get_eigen_vars_alist ts =
  List.map (fun v -> ((term_to_var v).name, v))
    (find_var_refs Eigen (List.map obj_to_term ts))

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
    List.map (replace_lppterm_vars fresh_names) ts

let term_case term clauses used =
  let initial_state = save_state () in
    List.fold_right
      (fun (head, body) result ->
         match freshen_capital_vars Eigen (head::body) used with
           | [] -> assert false
           | fresh_head::fresh_body ->
               try
                 left_object_unify fresh_head term ;
                 let used_vars =
                   get_eigen_vars_alist (fresh_head::fresh_body) in
                 let subst = get_subst initial_state in
                 let restore () = (restore_state initial_state ;
                                   apply_subst subst) in
                   restore_state initial_state ;
                   match term with
                     | Obj(_, r) when r <> Irrelevant ->
                         (restore, used_vars, List.map
                            (apply_restriction Smaller) fresh_body)::result
                     | _ -> (restore, used_vars, fresh_body)::result
               with
                 | Unify.Error _ ->
                     restore_state initial_state ;
                     result)
      clauses []

let case term clauses used =
  match term with
    | Obj _ -> term_case term clauses used
    | Or(left, right) ->
        let initial_state = save_state () in
        let restore () = restore_state initial_state in
          [(restore, [], [left]) ;
           (restore, [], [right])]
    | _ -> invalid_lppterm_arg term

let rec apply_restriction_at res stmt arg =
  match stmt with
    | Arrow(left, right) ->
        if arg = 1 then
          Arrow(apply_restriction res left, right)
        else
          Arrow(left, apply_restriction_at res right (arg-1))
    | _ -> failwith "Not enough implications in induction"
      
let induction ind_arg stmt =
  match stmt with
    | Forall(bindings, body) ->
        let ih_body = apply_restriction_at Smaller body ind_arg in
        let goal_body = apply_restriction_at Equal body ind_arg in
          (forall bindings ih_body, forall bindings goal_body)
    | _ -> failwith "Induction applied to non-forall statement"

let is_obj t =
  match t with
    | Obj _ -> true
    | _ -> false

let search n goal clauses used hyps =
  let rec term_aux n goal =
    if List.exists (try_right_object_unify goal)
      (List.filter is_obj hyps) then
        true
    else if n = 0 then
      false
    else
      List.exists
        (fun (head, body) ->
           try_with_state
             (fun () ->
                match freshen_capital_vars Logic (head::body) used with
                  | [] -> assert false
                  | fresh_head::fresh_body ->
                      right_object_unify fresh_head goal ;
                      List.for_all (term_aux (n-1)) fresh_body))
        clauses
  in
  let rec lppterm_aux goal =
    match goal with
      | Or(left, right) -> lppterm_aux left or lppterm_aux right
      | _ -> term_aux n goal
  in
    lppterm_aux goal


