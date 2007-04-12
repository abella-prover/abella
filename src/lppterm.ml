open Term
open Norm
open Pprint

type restriction = Smaller | Equal | Irrelevant

type lppterm =
  | Obj of term * restriction
  | Arrow of lppterm * lppterm
  | Forall of id list * lppterm
  | Or of lppterm * lppterm

let obj t = Obj(t, Irrelevant)
let obj_r t r = Obj(t, r)
let arrow a b = Arrow(a, b)
let forall ts t = Forall(ts, t)
let lpp_or a b = Or(a, b)

let obj_to_term t =
  match t with
    | Obj(t, _) -> t
    | _ -> failwith "obj_to_term called on non-obj"

let apply_restriction r t =
  match t with
    | Obj(t, _) -> Obj(t, r)
    | _ -> failwith "Attempting to apply restriction to non-object"

let restriction_to_string r =
  match r with
    | Smaller -> "*"
    | Equal -> "@"
    | Irrelevant -> ""

let bindings_to_string ts =
  String.concat " " ts

let lppterm_to_string t =
  let priority t =
    match t with
      | Obj _ -> 3
      | Or _ -> 2
      | Arrow _ -> 1
      | Forall _ -> 0
  in
  let rec aux pr t =
    let op_p = priority t in
    let pp =
      match t with
        | Obj(t, r) ->
            "{" ^ (term_to_string t) ^ "}" ^ (restriction_to_string r)
        | Arrow(a, b) ->
            (aux (op_p + 1) a) ^ " -> " ^ (aux op_p b)
        | Forall(ts, t) ->
            "forall " ^ (bindings_to_string ts) ^ ", " ^ (aux op_p t)
        | Or(a, b) ->
            (aux op_p a) ^ " or " ^ (aux (op_p + 1) b)
    in
      if op_p >= pr then pp else "(" ^ pp ^ ")"
  in
    aux 0 t

let invalid_lppterm_arg t =
  invalid_arg (lppterm_to_string t)
