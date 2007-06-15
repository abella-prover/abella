open Term
open Norm
open Pprint

type restriction = Smaller | Equal | Irrelevant

type lppterm =
  | Obj of Context.t * term * restriction
  | Arrow of lppterm * lppterm
  | Forall of id list * lppterm
  | Exists of id list * lppterm
  | Or of lppterm * lppterm

(* Constructions *)

let obj t = Obj(Context.empty, t, Irrelevant)
let arrow a b = Arrow(a, b)
let forall ids t = Forall(ids, t)
let exists ids t = Exists(ids, t)
let lpp_or a b = Or(a, b)

let context_obj ctx t = Obj(ctx, t, Irrelevant)

(* Queries *)
  
let is_obj t =
  match t with
    | Obj _ -> true
    | _ -> false

        
(* Manipulations *)
  
let obj_to_term t =
  match t with
    | Obj(_, t, _) -> t
    | _ -> failwith "obj_to_term called on non-obj"

let obj_to_restriction t =
  match t with
    | Obj(_, _, r) -> r
    | _ -> failwith "obj_to_restriction called on non-object"

let apply_restriction r t =
  match t with
    | Obj(c, t, _) -> Obj(c, t, r)
    | _ -> failwith "Attempting to apply restriction to non-object"

let add_to_context elt t =
  match t with
    | Obj(c, t, r) -> Obj(Context.add elt c, t, r)
    | _ -> failwith "Attempting to add context to non-object"

let replace_term_vars alist t =
  let rec aux t =
    match observe t with
        | Var {name=name} when List.mem_assoc name alist ->
            List.assoc name alist
        | Var _
        | DB _ -> t
        | Lam(i, t) -> lambda i (aux t)
        | App(t, ts) -> app (aux t) (List.map aux ts)
        | Susp _ -> failwith "Susp found during replace_term_vars"
        | Ptr _ -> assert false
  in
    aux t

let remove_assoc_list to_remove alist =
  let rec aux alist =
    match alist with
      | (a, b)::rest ->
          if List.mem a to_remove
          then aux rest
          else (a, b)::(aux rest)
      | [] -> []
  in
    aux alist
      
let rec replace_lppterm_vars alist t =
  let aux t = replace_lppterm_vars alist t in
    match t with
      | Obj([], t, r) -> Obj([], replace_term_vars alist t, r)
      | Obj(c, t, r) ->
          failwith "replace_term_vars called with non-empty context"
      | Arrow(a, b) -> Arrow(aux a, aux b)
      | Forall _ -> failwith "Cannot replace vars inside forall"
      | Exists(bindings, body) ->
          let alist' = remove_assoc_list bindings alist in
          let body' = replace_lppterm_vars alist' body in
            Exists(bindings, body')
      | Or(a, b) -> Or(aux a, aux b)

      
(* Pretty printing *)

let restriction_to_string r =
  match r with
    | Smaller -> "*"
    | Equal -> "@"
    | Irrelevant -> ""

let bindings_to_string ts =
  String.concat " " ts

let priority t =
  match t with
    | Obj _ -> 3
    | Or _ -> 2
    | Arrow _ -> 1
    | Forall _ -> 0
    | Exists _ -> 0
    
let lppterm_to_string t =
  let rec aux pr_above t =
    let pr_curr = priority t in
    let pp =
      match t with
        | Obj(c, t, r) ->
            if Context.is_empty c then
              "{" ^ (term_to_string t) ^ "}" ^ (restriction_to_string r)
            else
              "{" ^ (Context.context_to_string c) ^ " |- " ^
                (term_to_string t) ^ "}" ^ (restriction_to_string r)
        | Arrow(a, b) ->
            (aux (pr_curr + 1) a) ^ " -> " ^ (aux pr_curr b)
        | Forall(ids, t) ->
            "forall " ^ (bindings_to_string ids) ^ ", " ^ (aux pr_curr t)
        | Exists(ids, t) ->
            "exists " ^ (bindings_to_string ids) ^ ", " ^ (aux pr_curr t)
        | Or(a, b) ->
            (aux pr_curr a) ^ " or " ^ (aux (pr_curr + 1) b)
    in
      if pr_curr >= pr_above then pp else "(" ^ pp ^ ")"
  in
    aux 0 t


(* Error reporting *)

let invalid_lppterm_arg t =
  invalid_arg (lppterm_to_string t)

