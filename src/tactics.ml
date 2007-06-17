open Term
open Lppterm
open Pprint
open Unify

(* Unification utilities *)

let left_object_unify obj1 obj2 =
  left_unify obj1.term obj2.term

let right_object_unify obj1 obj2 =
  right_unify obj1.term obj2.term

let try_left_object_unify t1 t2 =
  try_with_state
    (fun () ->
       left_object_unify t1 t2 ;
       true)

let try_right_object_unify t1 t2 =
  try_with_state
    (fun () ->
       right_object_unify t1 t2 ;
       true)

(* Variable naming utilities *)

let fresh_alist tag ids used =
  let used = ref used in
    List.map (fun x ->
                let (fresh, curr_used) = fresh_wrt tag x !used in
                  used := curr_used ;
                  (x, fresh))
      ids
      
let get_term_vars_alist tag ts =
  List.map (fun v -> ((term_to_var v).name, v))
    (find_var_refs tag ts)

let get_lppterm_vars_alist tag ts =
  get_term_vars_alist tag
    (List.map (fun obj -> obj.term)
       (List.map term_to_obj ts))
    
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
          (map_vars_list (fun v -> v.name) ts))

let freshen_capital_vars tag ts used =
  let var_names = capital_var_names ts in
  let fresh_names = fresh_alist tag var_names used in
    List.map (replace_term_vars fresh_names) ts

let freshen_clause tag head body used =
  match freshen_capital_vars tag (head::body) used with
    | head::body -> head, body
    | _ -> assert false

let freshen_bindings tag bindings term used =
  replace_lppterm_vars (fresh_alist tag bindings used) term

(* Object level cut *)

let is_imp t =
  match observe t with
    | App(t, _) -> eq t (const "=>")
    | _ -> false

let extract_imp t =
  match observe t with
    | App(t, [a; b]) -> (a, b)
    | _ -> failwith "Check is_imp before calling extract_imp"
          
let object_cut obj1 obj2 =
  let a, b = extract_imp obj1.term in
    if eq a obj2.term then
      termobj b
    else
      failwith "Object cut applied to non-matching hypotheses"


(* Object level instantiation *)
        
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

let object_inst obj1 x =
  let t = obj1.term in
    if is_pi_abs t then
      termobj (Norm.deep_norm (app (extract_pi_abs t) [x]))
    else
      failwith ("Object instantiation requires a hypothesis of the form " ^
                  "{pi x\\ ...}")


(* Apply forall statement *)

let check_restrictions formal actual =
  List.iter2 (fun fr ar -> match fr, ar with
                | Smaller, Equal
                | Smaller, Irrelevant ->
                    failwith "Restriction violated"
                | _ -> ())
    formal actual

let rec map_args f t =
  match t with
    | Arrow(left, right) ->
        (f left) :: (map_args f right)
    | _ -> []

let term_to_restriction t =
  match t with
    | Obj(_, r) -> r
    | _ -> failwith "term_to_restriction called on non-object"
        
let apply_forall stmt ts =
  match stmt with
    | Forall(bindings, body) ->
        let fresh_body = freshen_bindings Logic bindings body [] in
        let formal = map_args term_to_restriction fresh_body in
        let actual = List.map term_to_restriction ts in
          check_restrictions formal actual ;
          List.fold_left
            (fun stmt arg ->
               match stmt, arg with
                 | Arrow(Obj(obj_left, _), right), Obj(obj_arg, _) ->
                     if not (Context.is_empty obj_left.context &&
                               Context.is_empty obj_arg.context) then
                       failwith "apply_forall with non-empty contexts" ;
                     begin try right_object_unify obj_left obj_arg with
                       | Unify.Error _ -> failwith "Unification failure"
                     end ;
                     right
                 | _ -> failwith "Too few implications in forall application")
            fresh_body
            ts
    | _ -> failwith "apply_forall can only be used on Forall(...) statements"


(* Case analysis *)

type case = {
  set_state : unit -> unit ;
  new_vars : (id * term) list ;
  new_hyps : lppterm list ;
}

let collect_some f list =
  List.map (fun x ->
              match x with
                | Some y -> y
                | _ -> assert false)
    (List.filter (fun x -> x <> None)
       (List.map f list))

let set_current_state () =
  let current_state = save_state () in
    (fun () -> restore_state current_state)

let obj_case obj r clauses used =
  if is_imp obj.term then
    let a, b = extract_imp obj.term in
      [{ set_state = set_current_state () ;
         new_vars = [] ;
         new_hyps =
           [ Obj({context = Context.add a obj.context ; term = b},
                 reduce_restriction r) ]
       }]
  else
    collect_some
      (fun (head, body) ->
         let fresh_head, fresh_body = freshen_clause Eigen head body used in
         let initial_state = save_state () in
           if try_left_unify fresh_head obj.term then
             let new_vars = get_term_vars_alist Eigen (fresh_head::fresh_body) in
             let subst = get_subst initial_state in
             let set_state () = (restore_state initial_state ; apply_subst subst) in
             let contexted_body = List.map (context_obj obj.context) fresh_body in
             let restricted_body =
               List.map (fun obj -> Obj(obj, reduce_restriction r)) contexted_body
             in
               restore_state initial_state ;
               Some { set_state = set_state ;
                      new_vars = new_vars ;
                      new_hyps = restricted_body }
           else
             None)
      clauses

let case term clauses used =
  match term with
    | Obj(obj, r) -> obj_case obj r clauses used
    | Or(left, right) ->
        let make_simple_case h =
          { set_state = set_current_state () ;
            new_vars = [] ; new_hyps = [h] }
        in
          [make_simple_case left; make_simple_case right]
    | Exists(ids, body) ->
        let fresh_ids = fresh_alist Eigen ids used in
        let fresh_body = replace_lppterm_vars fresh_ids body in
          [{ set_state = set_current_state () ;
             new_vars = fresh_ids ;
             new_hyps = [fresh_body] }]
    | _ -> invalid_lppterm_arg term


(* Induction *)

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


(* Search *)

let derivable goal hyp =
  Context.subcontext hyp.context goal.context &&
    try_right_unify goal.term hyp.term

let search n goal clauses hyps =
  let rec term_aux n used goal =
    if List.exists (derivable goal) (filter_objs hyps) then
        true
    else if Context.exists (try_right_unify goal.term) goal.context then
      true
    else if n = 0 then
      false
    else if is_imp goal.term then
      let a, b = extract_imp goal.term in
        term_aux (n-1) used {context = Context.add a goal.context ; term = b}
    else
      List.exists
        (fun (head, body) ->
           try_with_state
             (fun () ->
                let fresh_head, fresh_body =
                  freshen_clause Logic head body used
                in
                  right_unify fresh_head goal.term ;
                  let curr_used =
                    List.map fst (get_term_vars_alist Logic fresh_body)
                  in
                  let contexted_body =
                    List.map (fun t -> {goal with term = t}) fresh_body
                  in
                    List.for_all (term_aux (n-1) curr_used) contexted_body))
        clauses
  in
  let rec lppterm_aux goal =
    match goal with
      | Or(left, right) -> lppterm_aux left or lppterm_aux right
      | Exists(bindings, body) ->
          let term = freshen_bindings Logic bindings body [] in
          let used = List.map fst (get_lppterm_vars_alist Logic [term]) in
            lppterm_aux term
      | Obj(obj, r) -> term_aux n [] obj
      | _ -> false
  in
    lppterm_aux goal
