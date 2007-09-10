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
  terms
  |> map_vars_list (fun v -> v.name)
  |> List.find_all is_capital
  |> List.unique

let lpp_capital_var_names lppterms =
  lppterms
  |> List.map collect_terms
  |> List.flatten
  |> capital_var_names

let freshen_clause ~tag ~used ?(support=[]) head body =
  let var_names = capital_var_names (head::body) in
  let fresh_names = fresh_alist ~support ~tag ~used var_names in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = List.map (replace_term_vars fresh_names) body in
    (fresh_head, fresh_body)

let freshen_meta_clause ~tag ~used ?(support=[]) head body =
  let var_names = lpp_capital_var_names (pred head :: body) in
  let fresh_names = fresh_alist ~tag ~used var_names in
  let used =
    List.map (fun (_, t) -> ((term_to_var t).name, t)) fresh_names @ used in
  let raised_names = raise_alist ~support fresh_names in
  let fresh_head = replace_term_vars raised_names head in
  let fresh_body = List.map (replace_lppterm_vars raised_names) body in
    (used, fresh_head, fresh_body)

let freshen_bindings ?(support=[]) ~tag ~used bindings term =
  term |> replace_lppterm_vars (fresh_alist ~support ~tag ~used bindings)

let term_vars_alist tag terms =
  terms
  |> find_var_refs tag
  |> List.map (fun v -> ((term_to_var v).name, v))
    
let lppterm_vars_alist tag lppterms =
  lppterms
  |> List.map collect_terms
  |> List.flatten
  |> term_vars_alist tag
      
(* Freshening for Logic variables uses anonymous names *)
      
let fresh_nameless_alist ?(support=[]) ~tag ids =
  ids |> List.map (fun x -> (x, app (fresh ~tag 0) support))
      
let freshen_nameless_clause ?(support=[]) head body =
  let var_names = capital_var_names (head::body) in
  let fresh_names = fresh_nameless_alist ~tag:Logic ~support var_names in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = List.map (replace_term_vars fresh_names) body in
    (fresh_head, fresh_body)

let freshen_nameless_meta_clause ?(support=[]) ~tag head body =
  let var_names = lpp_capital_var_names (pred head :: body) in
  let fresh_names = fresh_nameless_alist ~tag ~support var_names in
  let fresh_head = replace_term_vars fresh_names head in
  let fresh_body = List.map (replace_lppterm_vars fresh_names) body in
    (fresh_head, fresh_body)

let freshen_nameless_bindings ?(support=[]) ~tag bindings term =
  term |> replace_lppterm_vars (fresh_nameless_alist ~support ~tag bindings)

(* Object level cut *)

(* obj1 = L1 |- A
   obj2 = L2, A |- C
   result = L2, L1 |- C *)
let object_cut obj1 obj2 =
  let ctx =
    obj1.context
    |> Context.remove obj2.term
    |> Context.union obj2.context
    |> Context.normalize 
  in
    Obj(context_obj ctx obj1.term, Irrelevant)

(* Object level instantiation *)
        
let object_inst obj name term =
  map_obj (replace_term_vars [(name, term)]) obj

(* Case analysis *)

type case = {
  bind_state : bind_state ;
  new_vars : (id * term) list ;
  new_hyps : lppterm list ;
}

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

let meta_term_case ~support ~used ~meta_clauses ~wrapper term =
  meta_clauses|> List.filter_map
      (fun (head, body) ->
         let initial_state = get_bind_state () in
         let initial_used = used in
         let used, head, body =
           match head with
             | Pred(p, _) -> used, p, body
             | Binding(Nabla, [id], Pred(p, _)) ->
                 let n = nominal_var "n1" in
                 let alist = [(id, n)] in
                   (lift_all ~used [n],
                    replace_term_vars alist p,
                    List.map (replace_lppterm_vars alist) body)
             | _ -> failwith "Bad head in meta-clause"
         in
         let used, head, body =
           freshen_meta_clause ~support ~tag:Eigen ~used head body
         in
           if try_left_unify ~used head term then
             let bind_state = get_bind_state () in
             let wrapped_body = List.map wrapper body in
             let used = List.unique
             ((List.find_all (fun (_, t) -> is_free t) used) @ initial_used)
             in
               set_bind_state initial_state ;
               Some { bind_state = bind_state ;
                      new_vars = used ;
                      new_hyps = wrapped_body }
           else
             (set_bind_state initial_state ; None))
      
let term_case ~support ~used ~clauses ~wrapper term =
  clauses |> List.filter_map
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

let obj_case ~used obj r clauses =
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
    | Binding(Nabla, [id], body) ->
        let nominal = fresh_nominal body in
        let fresh_body = replace_lppterm_vars [(id, nominal)] body in
          [{ bind_state = get_bind_state () ;
             new_vars = [] ;
             new_hyps = [fresh_body] }]
    | Pred(p, r) ->
        let wrapper t =
          let rec aux t =
            match t with
              | Pred(p, _) -> Pred(p, reduce_restriction r)
              | Binding(binding, ids, body) ->
                  Binding(binding, ids, aux body)
              | Or(t1, t2) -> Or(aux t1, aux t2)
              | And(t1, t2) -> And(aux t1, aux t2)
              | Arrow(t1, t2) -> Arrow(t1, aux t2)
              | Obj _ -> t
          in
            aux t
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
      | Binding(Nabla, [id], body) ->
        let nominal = fresh_nominal body in
        let body = replace_lppterm_vars [(id, nominal)] body in
          lppterm_aux n body
      | Arrow(Pred(left, _), right) when is_false right ->
          negative_meta_aux n left
      | Obj(obj, _) -> obj_aux n obj
      | Pred(p, _) ->
          List.exists (try_right_unify p) (filter_preds hyps) ||
            meta_aux n p
      | _ -> false

  and meta_aux n goal =
    if n = 0 then false else
      meta_clauses |> List.exists
          (fun (head, body) ->
             try_with_state
               (fun () ->
                  let support = term_support goal in
                  let head, body =
                    match head with
                      | Pred(p, _) -> p, body
                      | Binding(Nabla, [id], Pred(p, _)) ->
                          let n = nominal_var "n1" in
                          let alist = [(id, n)] in
                            (replace_term_vars alist p,
                             List.map (replace_lppterm_vars alist) body)
                      | _ -> failwith "Bad head in meta-clause"
                  in
                  let head, body =
                    freshen_nameless_meta_clause ~tag:Logic ~support head body
                  in
                    right_unify head goal ;
                    List.for_all (lppterm_aux (n-1)) body))
              
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
          meta_clauses |> List.for_all
              (fun (head, body) ->
                 try_with_state ~default:true
                   (fun () ->
                      let support = term_support goal in
                      let head, body =
                        match head with
                          | Pred(p, _) -> p, body
                          | Binding(Nabla, [id], Pred(p, _)) ->
                              let n = nominal_var "n1" in
                              let alist = [(id, n)] in
                                (replace_term_vars alist p,
                                 List.map (replace_lppterm_vars alist) body)
                          | _ -> failwith "Bad head in meta-clause"
                      in
                      let head, body =
                        freshen_nameless_meta_clause
                          ~tag:Eigen ~support head body
                      in
                      let body =
                        List.filter_map (fun t ->
                                           match t with
                                             | Pred(p, _) -> Some p
                                             | _ -> None)
                          body
                      in
                        left_unify head goal ;
                        List.exists (aux (n-1)) body))
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
    args
    |> List.map (Option.map_default lppterm_support [])
    |> List.flatten
    |> List.unique
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
      
let unfold ~used ~meta_clauses term =
  match term with
    | Pred(term, _) ->
        meta_clauses |> find_as
            (fun (head, body) ->
               let used, head, body =
                 match head with
                   | Pred(p, _) -> used, p, body
                   | _ -> failwith "Bad head in meta-clause"
               in
               let used, head, body =
                 freshen_meta_clause ~tag:Logic ~used head body
               in
                 if try_right_unify ~used head term then
                   Some body
                 else
                   None)
    | _ -> failwith "Can only unfold predicates"
