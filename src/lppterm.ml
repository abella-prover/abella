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

let rec lppterm_to_string t =
  match t with
    | Obj(t, r) -> "{" ^ (term_to_string t) ^ "}" ^
        (restriction_to_string r)
    | Arrow(a, b) -> (lppterm_to_string a) ^ " -> " ^ (lppterm_to_string b)
    | Forall(ts, t) ->
        "forall " ^ (bindings_to_string ts) ^ ", " ^ (lppterm_to_string t)
    | Or(a, b) ->
        (lppterm_to_string a) ^ " or " ^ (lppterm_to_string b)

let invalid_lppterm_arg t =
  invalid_arg (lppterm_to_string t)
