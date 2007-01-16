open Term
open Norm
open Pprint

type restriction = int * bool

type lppterm =
  | Obj of term list * term * restriction
  | Arrow of lppterm * lppterm
  | Forall of id list * lppterm

let obj t = Obj([], t, (0, false))
let arrow a b = Arrow(a, b)
let forall ts t = Forall(ts, t)

let inactive_obj t r = Obj([], t, (r, false))
let active_obj t r = Obj([], t, (r, true))
let obj_r t r = Obj([], t, r)

let context_obj c t = Obj(c, t, (0, false))

let obj_to_term t =
  match t with
    | Obj(_, t, _) -> t
    | _ -> failwith "obj_to_term called on non-obj"

let apply_active_restriction n t =
  match t with
    | Obj(c, t, _) -> Obj(c, t, (n, true))
    | _ -> failwith "Attempting to apply restriction to non-object"

let restriction_to_string (n, active) =
  if active then String.make n '*' else String.make n '@'

let bindings_to_string ts =
  String.concat " " ts

let rec lppterm_to_string t =
  match t with
    | Obj([], t, r) -> "{" ^ (term_to_string t) ^ "}" ^
        (restriction_to_string r)
    | Obj(c, t, r) -> "{" ^ (String.concat ", " (List.map term_to_string c)) ^
        " |- " ^ (term_to_string t) ^ "}" ^ (restriction_to_string r)
    | Arrow(a,b) -> (lppterm_to_string a) ^ " -> " ^ (lppterm_to_string b)
    | Forall(ts, t) ->
        "forall " ^ (bindings_to_string ts) ^ ", " ^ (lppterm_to_string t)
