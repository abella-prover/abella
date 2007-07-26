open Term
open Lppterm
open Unify
open Extensions

(* Variable naming utilities *)

let is_capital str =
  match str.[0] with
    | 'A'..'Z' -> true
    | _ -> false

let capital_var_names terms =
  let names = map_vars_list (fun v -> v.name) terms in
    List.unique (List.find_all is_capital names)

let lpp_capital_var_names lppterms =
  let terms = List.flatten (List.map collect_terms lppterms) in
    capital_var_names terms

let freshen_clause ~tag ~used ?(support=[]) head body =
  let var_names = capital_var_names (head::body) in
  let fresh_names = fresh_alist ~support ~tag ~used var_names in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = List.map (replace_term_vars fresh_names) body in
    (fresh_head, fresh_body)

let freshen_meta_clause ~tag ~used ?(support=[]) head body =
  let var_names = lpp_capital_var_names (head :: body) in
  let fresh_names = fresh_alist ~support ~tag ~used var_names in
  let fresh_head = replace_lppterm_vars fresh_names head in
  let fresh_body = List.map (replace_lppterm_vars fresh_names) body in
    (fresh_head, fresh_body)

let freshen_bindings ?(support=[]) ~tag ~used bindings term =
  replace_lppterm_vars
    (fresh_alist ~support ~tag ~used bindings)
    term

let term_vars_alist tag terms =
  List.map (fun v -> ((term_to_var v).name, v))
    (find_var_refs tag terms)
    
let lppterm_vars_alist tag lppterms =
  let terms = List.flatten (List.map collect_terms lppterms) in
    term_vars_alist tag terms

(* Freshening for Logic variables uses anonymous names *)

let fresh_nameless_alist ?(support=[]) ~tag ids =
  List.map (fun x -> (x, app (fresh ~tag 0) support)) ids
      
let freshen_logic_clause ?(support=[]) head body =
  let var_names = capital_var_names (head::body) in
  let fresh_names = fresh_nameless_alist ~tag:Logic ~support var_names in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = List.map (replace_term_vars fresh_names) body in
    (fresh_head, fresh_body)

let freshen_nameless_meta_clause ?(support=[]) ~tag head body =
  let var_names = lpp_capital_var_names (head :: body) in
  let fresh_names = fresh_nameless_alist ~tag ~support var_names in
  let fresh_head = replace_lppterm_vars fresh_names head in
  let fresh_body = List.map (replace_lppterm_vars fresh_names) body in
    (fresh_head, fresh_body)

let freshen_nameless_bindings ?(support=[]) ~tag bindings term =
  replace_lppterm_vars (fresh_nameless_alist ~support ~tag bindings) term

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

let meta_term_case ~support ~used ~meta_clauses ~wrapper term =
  List.filter_map
    (fun (head, body) ->
       let fresh_head, fresh_body =
         freshen_meta_clause ~support ~tag:Eigen ~used head body in
       let unwrapped_head =
         match fresh_head with
           | Pred(p, _) -> p
           | _ -> failwith "Bad head in meta-clause"
       in
       let initial_state = get_bind_state () in
         if try_left_unify ~used unwrapped_head term then
           let new_vars =
             lppterm_vars_alist Eigen (pred unwrapped_head::fresh_body) in
           let bind_state = get_bind_state () in
           let wrapped_body = List.map wrapper fresh_body in
             set_bind_state initial_state ;
             Some { bind_state = bind_state ;
                    new_vars = new_vars ;
                    new_hyps = wrapped_body }
         else
               None)
    meta_clauses
      
let term_case ~support ~used ~clauses ~wrapper term =
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
      normalize (Obj(context_obj obj.context t, reduce_restriction r)) in
    let support = obj_support obj in
    let clause_cases =
      term_case ~support ~used ~clauses ~wrapper obj.term in
    let member_case =
      { bind_state = get_bind_state () ;
        new_vars = [] ;
        new_hyps = [obj_to_member obj] }
    in
      if Context.is_empty obj.context then
        clause_cases
      else
        member_case :: clause_cases

let case ~used ~clauses ~meta_clauses term =
  match term with
    | Obj(obj, r) -> obj_case ~used obj r clauses
    | Or(left, right) ->
        let make_simple_case h =
          { bind_state = get_bind_state () ;
            new_vars = [] ; new_hyps = [h] }
        in
          [make_simple_case left; make_simple_case right]
    | And(left, right) ->
        [{ bind_state = get_bind_state () ;
           new_vars = [] ; new_hyps = [left; right] }]
    | Binding(Exists, ids, body) ->
        let fresh_ids = fresh_alist ~used ~tag:Eigen ids in
        let fresh_body = replace_lppterm_vars fresh_ids body in
          [{ bind_state = get_bind_state () ;
             new_vars = fresh_ids ;
             new_hyps = [fresh_body] }]
    | Pred(p, r) ->
        let wrapper t =
          match t with
            | Pred(p, _) -> Pred(p, reduce_restriction r)
            | _ -> t
        in
          meta_term_case ~used ~support:(term_support p)
            ~meta_clauses ~wrapper p
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
      | And(a, b) -> max (aux a) (aux b)
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
  match t with
    | Pred(p, _) ->
        begin match observe p with
          | Var {name=f} when f = "false" -> true
          | _ -> false
        end
    | _ -> false

let search ~depth:n ~hyps ~clauses ~meta_clauses goal =
  
  let rec term_aux n context goal =
    List.exists
      (fun (head, body) ->
         try_with_state
           (fun () ->
              let support = term_support goal in
              let fresh_head, fresh_body =
                freshen_logic_clause ~support head body
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
      let context_search () =
        not (Context.is_empty goal.context) &&
          lppterm_aux (n-1) (obj_to_member goal)
      in
      let backchain () =
        term_aux n goal.context goal.term
      in
        context_search () || backchain ()
        
  and lppterm_aux n goal =
    match goal with
      | Or(left, right) -> lppterm_aux n left || lppterm_aux n right
      | And(left, right) -> lppterm_aux n left && lppterm_aux n right
      | Binding(Exists, bindings, body) ->
          let term = freshen_nameless_bindings ~tag:Logic bindings body in
            lppterm_aux n term
      | Binding(Forall, bindings, body) ->
          let term = freshen_nameless_bindings ~tag:Eigen bindings body in
            lppterm_aux n term
      | Arrow(Pred(left, _), right) when is_false right ->
          negative_meta_aux n left
      | Obj(obj, _) -> obj_aux n obj
      | Pred(p, _) ->
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
                  freshen_nameless_meta_clause ~tag:Logic ~support head body
                in
                let unwrapped_head =
                  match fresh_head with
                    | Pred(p, _) -> p
                    | _ -> failwith "Bad head in meta-clause"
                in
                  right_unify unwrapped_head goal ;
                  List.for_all (lppterm_aux (n-1)) fresh_body))
        meta_clauses
              
  (* true if we can confirm no proof exists *)
  and negative_meta_aux n goal =
    let table = ref [] in
    let rec aux n goal =
      if n = 0 then
        false
      else
        let table () =
          let abs_goal = abstract_eigen goal in
            if List.mem ~cmp:eq abs_goal !table then
              true
            else
              begin
                table := abs_goal :: !table ;
                false
              end
        in
        let backchain () =
          List.for_all
            (fun (head, body) ->
               try_with_state ~default:true
                 (fun () ->
                    let support = term_support goal in
                    let fresh_head, fresh_body =
                      freshen_nameless_meta_clause ~tag:Eigen ~support head body
                    in
                    let unwrapped_head =
                      match fresh_head with
                        | Pred(p, _) -> p
                        | _ -> failwith "Bad head in meta-clause"
                    in
                    let pred_body =
                      List.filter_map (fun t ->
                                         match t with
                                           | Pred(p, _) -> Some p
                                           | _ -> None)
                        fresh_body
                    in
                      left_unify unwrapped_head goal ;
                      List.exists (aux (n-1)) pred_body))
            meta_clauses
        in
          table () || backchain ()
    in
    let bind_state = Term.get_bind_state () in
    let result = aux n goal in
      set_bind_state bind_state ;
      result
        
  in
    lppterm_aux n goal

      
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
    List.unique (List.flatten (List.map
                                 (Option.map_default lppterm_support []) args))
  in
  let rec aux term =
    match term with
      | Binding(Forall, bindings, body) ->
          aux (freshen_nameless_bindings ~tag:Logic ~support bindings body)
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
                         right_unify left.term arg.term ;
                         right
                     | Arrow(Pred(left, _), right), Some (Pred(arg, _)) ->
                         right_unify left arg ;
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
