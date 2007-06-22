open Term
open Lppterm
open Unify

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
    
let lppterm_capital_var_names t =
  let names = List.flatten (map_term_list (fun t -> map_vars_list (fun v -> v.name) [t]) t)
  in
  let capital_names = List.filter is_capital names in
    uniq capital_names

let freshen_lppterm_capital_vars tag t used =
  let var_names = lppterm_capital_var_names t in
  let fresh_names = fresh_alist tag var_names used in
    replace_lppterm_vars fresh_names t
    
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
      termobj (deep_norm (app (extract_pi_abs t) [x]))
    else
      failwith ("Object instantiation requires a hypothesis of the form " ^
                  "{pi x\\ ...}")


(* Apply forall statement *)


let has_restrictions res_list =
  List.exists (fun r -> r <> Irrelevant) res_list
    
let check_restrictions formal actual =
  if has_restrictions formal then
    let level = ref (List.length formal) in
    let one_smaller = ref false in
      List.iter2 (fun fr ar -> match fr, ar with
                    | Smaller i, Smaller j when i = j ->
                        level := min !level i ;
                        one_smaller := true
                    | Smaller i, Equal j when i = j ->
                        ()
                    | Smaller i, _ ->
                        level := min !level (i - 1)
                    | Irrelevant, _ -> ()
                    | _, _ -> failwith "Bad restriction")
        formal actual ;
      if !level = 0 || not !one_smaller then failwith "Restriction violated"

let rec map_args f t =
  match t with
    | Arrow(left, right) ->
        (f left) :: (map_args f right)
    | _ -> []

let term_to_restriction t =
  match t with
    | Obj(_, r) -> r
    | _ -> Irrelevant
        
let apply_forall stmt ts =
  match stmt with
    | Forall(bindings, body) ->
        let fresh_body = freshen_bindings Logic bindings body [] in
        let formal = map_args term_to_restriction fresh_body in
        let actual = List.map term_to_restriction ts in
        let context_pairs = ref [] in
          check_restrictions formal actual ;
          let result =
            List.fold_left
              (fun stmt arg ->
                 match stmt, arg with
                   | Arrow(Obj(left, _), right), Obj(arg, _) ->
                       context_pairs :=
                         (left.context, arg.context)::!context_pairs ;
                       begin try right_unify left.term arg.term with
                         | Unify.Error _ -> failwith "Unification failure"
                       end ;
                       right
                   | Arrow(Pred(left), right), Pred(arg) ->
                       begin try right_unify left arg with
                         | Unify.Error _ -> failwith "Unificaion failure"
                       end ;
                       right
                   | _ -> failwith "Too few implications in forall application")
              fresh_body
              ts
          in
            Context.reconcile !context_pairs ;
            normalize result
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

let term_case term clauses used wrapper =
  collect_some
    (fun (head, body) ->
       let fresh_head, fresh_body = freshen_clause Eigen head body used in
       let initial_state = save_state () in
         if try_left_unify fresh_head term then
           let new_vars = get_term_vars_alist Eigen (fresh_head::fresh_body) in
           let subst = get_subst initial_state in
           let set_state () = (restore_state initial_state ;
                               apply_subst subst)
           in
           let wrapped_body = List.map wrapper fresh_body in
             restore_state initial_state ;
             Some { set_state = set_state ;
                        new_vars = new_vars ;
                        new_hyps = wrapped_body }
         else
               None)
    clauses
      
let obj_case obj r clauses used =
  if is_imp obj.term then
    [{ set_state = set_current_state () ;
       new_vars = [] ;
       new_hyps = [ Obj(move_imp_to_context obj, reduce_restriction r) ]
     }]
  else 
    let wrapper t =
      normalize (Obj(context_obj obj.context t, reduce_restriction r))
    in
    let clause_cases = term_case obj.term clauses used wrapper in
    let member_case =
      { set_state = set_current_state () ;
        new_vars = [] ;
        new_hyps = [obj_to_member obj] }
    in
      if Context.is_empty obj.context then
        clause_cases
      else
        member_case :: clause_cases

let parse_clauses str =
  Parser.clauses Lexer.token (Lexing.from_string str)

let meta_clauses =
  ref (parse_clauses "member A (A :: L). member A (B :: L) :- member A L.")
      
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
    | Pred(p) ->
        let wrapper t = Pred(t) in
          term_case p !meta_clauses used wrapper
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

let apply_restrictions ind_args body res_f =
  let count = ref 0 in
  List.fold_left
    (fun term ind ->
       incr count; apply_restriction_at (res_f !count) term ind)
    body ind_args
        
let induction ind_args stmt =
  match stmt with
    | Forall(bindings, body) ->
        let ih = apply_restrictions ind_args body (fun i -> Smaller i) in
        let goal = apply_restrictions ind_args body (fun i -> Equal i) in
          (forall bindings ih, forall bindings goal)
    | _ -> failwith "Induction applied to non-forall statement"


(* Search *)

let derivable goal hyp =
  try_right_unify goal.term hyp.term &&
    Context.subcontext hyp.context goal.context

let search n goal clauses hyps =
  let rec term_aux n used clauses goal next =
    List.exists
      (fun (head, body) ->
         try_with_state
           (fun () ->
              let fresh_head, fresh_body =
                freshen_clause Logic head body used
              in
                right_unify fresh_head goal ;
                let curr_used =
                  List.map fst (get_term_vars_alist Logic fresh_body)
                in
                  List.for_all (next (n-1) curr_used) fresh_body))
      clauses
  and obj_aux n used goal =
    if List.exists (derivable goal) (filter_objs hyps) then
      true
    else if Context.exists (try_right_unify goal.term) goal.context then
      true
    else if n = 0 then
      false
    else if is_imp goal.term then
      obj_aux (n-1) used (move_imp_to_context goal)
    else
      ((not (Context.is_empty goal.context)) &&
         lppterm_aux (n-1) used (obj_to_member goal))
      || (term_aux n used clauses goal.term
            (fun n used t -> obj_aux n used {goal with term=t}))
  and lppterm_aux n used goal =
    match goal with
      | Or(left, right) -> lppterm_aux n used left or lppterm_aux n used right
      | Exists(bindings, body) ->
          let term = freshen_bindings Logic bindings body [] in
          let used = List.map fst (get_lppterm_vars_alist Logic [term]) in
            lppterm_aux n used term
      | Obj(obj, r) -> obj_aux n used obj
      | Pred(p) ->
          List.exists (try_right_unify p) (filter_preds hyps) ||
            term_aux n used !meta_clauses p
            (fun n used t -> lppterm_aux n used (Pred t))
      | _ -> false
  in
    lppterm_aux n [] goal
