open Term
open Lppterm
open Pprint

let is_imp t =
  match observe t with
    | App(t, _) -> eq t (atom "=>")
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
    | App(t, [abs]) -> eq t (atom "pi") &&
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

let fresh_alist ?(tag=Logic) ts =
  List.map (fun x -> (x, fresh ~name:x ~tag:tag 0)) ts

let replace_vars alist t =
  let rec aux_term t =
    match observe t with
      | Var {name=name} when List.mem_assoc name alist ->
          List.assoc name alist
      | Var _
      | DB _
      | NB _ -> t
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
        let alist = fresh_alist (List.map fst bindings) in
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
        
let case term clauses =
  let initial_state = save_state () in
    List.fold_right
      (fun (head, body) result ->
         let var_names = logic_var_names (head::body) in
         let fresh_names = fresh_alist ~tag:Eigen var_names in
         let freshen = replace_vars fresh_names in
         let fresh_head = freshen head in
         let fresh_body = List.map freshen body in
           try
             right_object_unify fresh_head term ;
             let subst = get_subst initial_state in
             let restore () = (restore_state initial_state ;
                               ignore (apply_subst subst)) in
               restore_state initial_state ;
               match term with
                 | Obj(_, (n, _)) when n > 0 ->
                     (restore, List.map
                        (apply_active_restriction n) fresh_body)::result
                 | _ -> (restore, fresh_body)::result
           with
             | Unify.Error _ -> result)
      clauses []
  
