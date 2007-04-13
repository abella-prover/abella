open Term
open Norm
open Pprint

type restriction = Smaller | Equal | Irrelevant

type lppterm =
  | Obj of term * restriction
  | Arrow of lppterm * lppterm
  | Forall of id list * lppterm
  | Or of lppterm * lppterm


(* Constructions *)

let obj t = Obj(t, Irrelevant)
let arrow a b = Arrow(a, b)
let forall ts t = Forall(ts, t)
let lpp_or a b = Or(a, b)


(* Queries *)
  
let is_obj t =
  match t with
    | Obj _ -> true
    | _ -> false

        
(* Manipulations *)
  
let obj_to_term t =
  match t with
    | Obj(t, _) -> t
    | _ -> failwith "obj_to_term called on non-obj"

let obj_to_restriction t =
  match t with
    | Obj(_, r) -> r
    | _ -> failwith "obj_to_restriction called on non-object"

let apply_restriction r t =
  match t with
    | Obj(t, _) -> Obj(t, r)
    | _ -> failwith "Attempting to apply restriction to non-object"

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

let replace_lppterm_vars alist t =
  let rec aux t =
    match t with
      | Obj(t, r) -> Obj(replace_term_vars alist t, r)
      | Arrow(a, b) -> Arrow(aux a, aux b)
      | Forall _ -> failwith "Cannot replace vars inside forall"
      | Or(a, b) -> Or(aux a, aux b)
  in
    aux t

      
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
    
let lppterm_to_string t =
  let rec aux pr_above t =
    let pr_curr = priority t in
    let pp =
      match t with
        | Obj(t, r) ->
            "{" ^ (term_to_string t) ^ "}" ^ (restriction_to_string r)
        | Arrow(a, b) ->
            (aux (pr_curr + 1) a) ^ " -> " ^ (aux pr_curr b)
        | Forall(ts, t) ->
            "forall " ^ (bindings_to_string ts) ^ ", " ^ (aux pr_curr t)
        | Or(a, b) ->
            (aux pr_curr a) ^ " or " ^ (aux (pr_curr + 1) b)
    in
      if pr_curr >= pr_above then pp else "(" ^ pp ^ ")"
  in
    aux 0 t

      
(* Error reporting *)

let invalid_lppterm_arg t =
  invalid_arg (lppterm_to_string t)

