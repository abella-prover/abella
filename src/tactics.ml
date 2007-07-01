open Term
open Lppterm
open Unify
open Extensions

(* Variable naming utilities *)

let fresh_alist ?(support=[]) ~used ~tag ids =
  let used = ref used in
    List.map (fun x ->
                let (fresh, curr_used) = fresh_wrt tag x !used in
                  used := curr_used ;
                  (x, app fresh support))
      ids
      
let is_capital str =
  match str.[0] with
    | 'A'..'Z' -> true
    | _ -> false

let capital_var_names terms =
  let names = map_vars_list (fun v -> v.name) terms in
    List.unique (List.find_all is_capital names)

let freshen_clause ~tag ~used ?(support=[]) head body =
  let var_names = capital_var_names (head::body) in
  let fresh_names = fresh_alist ~support ~tag ~used var_names in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = List.map (replace_term_vars fresh_names) body in
    (fresh_head, fresh_body)

let freshen_bindings ?(support=[]) ~tag ~used bindings term =
  replace_lppterm_vars
    (fresh_alist ~support ~tag ~used bindings)
    term

let term_vars_alist tag terms =
  List.map (fun v -> ((term_to_var v).name, v))
    (find_var_refs tag terms)

(* Object level cut *)

(* obj1 = L1 |- A
   obj2 = L2, A |- C
   result = L1, L2 |- C *)
let object_cut obj1 obj2 =
  let ctx =
    Context.union (Context.remove obj2.term obj1.context) obj2.context
  in
    Obj(context_obj ctx obj1.term, Irrelevant)

(* Object level instantiation *)
        
let object_inst obj name term =
  replace_obj_vars [(name, term)] obj

(* Case analysis *)

type case = {
  bind_state : bind_state ;
  new_vars : (id * term) list ;
  new_hyps : lppterm list ;
}

let term_case ~support ~used term clauses wrapper =
  List.filter_map
    (fun (head, body) ->
       let fresh_head, fresh_body =
         freshen_clause ~support ~tag:Eigen ~used head body in
       let initial_state = get_bind_state () in
         if try_left_unify ~used fresh_head term then
           let new_vars = term_vars_alist Eigen (fresh_head::fresh_body) in
           let bind_state = get_bind_state () in
           let wrapped_body = List.map wrapper fresh_body in
             set_bind_state initial_state ;
             Some { bind_state = bind_state ;
                    new_vars = new_vars ;
                    new_hyps = wrapped_body }
         else
               None)
    clauses
      
let obj_case ~used obj r clauses =
  if is_imp obj.term then
    [{ bind_state = get_bind_state () ;
       new_vars = [] ;
       new_hyps = [ Obj(move_imp_to_context obj, reduce_restriction r) ]
     }]
  else 
    let wrapper t =
      normalize (Obj(context_obj obj.context t, reduce_restriction r))
    in
    let support = obj_support obj in
    let clause_cases = term_case ~support ~used obj.term clauses wrapper in
    let member_case =
      { bind_state = get_bind_state () ;
        new_vars = [] ;
        new_hyps = [obj_to_member obj] }
    in
      if Context.is_empty obj.context then
        clause_cases
      else
        member_case :: clause_cases

let case ~used term clauses meta_clauses =
  match term with
    | Obj(obj, r) -> obj_case ~used obj r clauses
    | Or(left, right) ->
        let make_simple_case h =
          { bind_state = get_bind_state () ;
            new_vars = [] ; new_hyps = [h] }
        in
          [make_simple_case left; make_simple_case right]
    | Binding(Exists, ids, body) ->
        let fresh_ids = fresh_alist ~used ~tag:Eigen ids in
        let fresh_body = replace_lppterm_vars fresh_ids body in
          [{ bind_state = get_bind_state () ;
             new_vars = fresh_ids ;
             new_hyps = [fresh_body] }]
    | Pred(p) ->
        term_case ~used ~support:(term_support p) p meta_clauses pred
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

let get_max_restriction t =
  let rec aux t =
    match t with
      | Obj(_, Smaller n) -> n
      | Obj(_, Equal n) -> n
      | Obj(_, Irrelevant) -> 0
      | Arrow(a, b) -> max (aux a) (aux b)
      | Binding(_, _, body) -> aux body
      | Or(a, b) -> max (aux a) (aux b)
      | Pred _ -> 0
  in
    aux t
        
let induction ind_arg stmt =
  let rec aux stmt =
    match stmt with
      | Binding(Forall, bindings, body) ->
          let (ih, goal) = aux body in
            (forall bindings ih, forall bindings goal)
      | Binding(Nabla, bindings, body) ->
          let (ih, goal) = aux body in
            (nabla bindings ih, nabla bindings goal)
      | term ->
          let n = 1 + get_max_restriction term in
          let ih = apply_restriction_at (Smaller n) term ind_arg in
          let goal = apply_restriction_at (Equal n) term ind_arg in
            (ih, goal)
  in
    aux stmt

(* Search *)

let derivable goal hyp =
  try_right_unify goal.term hyp.term &&
    Context.subcontext hyp.context goal.context

let is_false t =
  begin match observe t with
    | Var {name=f} when f = "false" -> true
    | _ -> false
  end

let search ~depth:n ~hyps ~clauses ~meta_clauses ~goal ~used =
  
  let rec term_aux n context goal =
    List.exists
      (fun (head, body) ->
         try_with_state
           (fun () ->
              let fresh_head, fresh_body =
                freshen_clause ~used:[] ~tag:Logic head body
              in
                right_unify fresh_head goal ;
                List.for_all
                  (fun t -> obj_aux (n-1) {context=context; term=t})
                  fresh_body))
      clauses
      
  and obj_aux n goal =
    if List.exists (derivable goal) (filter_objs hyps) then
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
      ((not (Context.is_empty goal.context)) &&
         lppterm_aux (n-1) (obj_to_member goal))
      || (term_aux n goal.context goal.term)
        
  and lppterm_aux n goal =
    match goal with
      | Or(left, right) -> lppterm_aux n left or lppterm_aux n right
      | Binding(Exists, bindings, body) ->
          let term = freshen_bindings ~tag:Logic ~used bindings body in
            lppterm_aux n term
      | Obj(obj, r) -> obj_aux n obj
      | Pred(p) ->
          List.exists (try_right_unify p) (filter_preds hyps) ||
            meta_aux n p
      | _ -> false
          
  and meta_aux n goal =
    if n = 0 then false else
      List.exists
        (fun (head, body) ->
           try_with_state
             (fun () ->
                let support = term_support goal in
                let fresh_head, fresh_body =
                  freshen_clause ~support ~tag:Logic ~used head body
                in
                  right_unify fresh_head goal ;
                  List.for_all
                    (fun t -> lppterm_aux (n-1) (Pred t))
                    fresh_body))
        meta_clauses
      ||
        match observe goal with
          | App(head, body) ->
              begin match observe head, body with
                | Var {name=i}, [a; b] when i = "=>" ->
                    is_false b && negative_meta_aux n a
                      
                | Var {name=p}, [body] when p = "pi" ->
                    let var = fresh ~tag:Eigen 0 in
                    let goal = deep_norm (app body [var]) in
                      meta_aux (n-1) goal
                        
                | _ -> false
              end
          | _ -> false
              
  (* true if we can confirm no proof exists *)
  and negative_meta_aux n goal =
    match observe goal with
      | App(head, body) ->
          begin match observe head, body with
            | Var {name=e}, [a; b] when e = "=" ->
                not (try_left_unify a b)
            | _ -> false
          end
      | _ -> false
        
  in
    lppterm_aux n goal

      
(* Apply forall statement *)

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

let apply_forall term args =
  let support =
    List.unique (List.flatten (List.map
                                 (Option.map_default lppterm_support []) args))
  in
  let rec aux term =
    match term with
      | Binding(Forall, bindings, body) ->
          aux (freshen_bindings ~support ~tag:Logic ~used:[] bindings body)
      | Binding(Nabla, bindings, body) ->
          aux (freshen_bindings ~tag:Nominal ~used:[] bindings body)
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
                         begin try right_unify left.term arg.term with
                           | Unify.Error _ -> failwith "Unification failure"
                         end ;
                         right
                     | Arrow(Pred(left), right), Some (Pred arg) ->
                         begin try right_unify left arg with
                           | Unify.Error _ -> failwith "Unificaion failure"
                         end ;
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
