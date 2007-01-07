open Term
open Pprint

type restriction = int

type lppterm =
  | Obj of term * restriction
  | Arrow of lppterm * lppterm
  | Forall of (term * term) list * lppterm

let obj t = Obj(t, 0)
let arrow a b = Arrow(a, b)
let forall ts t = Forall(ts, t)

let obj_r t r = Obj(t, r)

let binding_to_string (tm, ty) =
  "(" ^ (term_to_string tm) ^ " : " ^ (term_to_string ty) ^ ")"

let bindings_to_string ts =
  String.concat " " (List.map binding_to_string ts)

let nstars n = String.make n '*'
    
let rec lppterm_to_string t =
  match t with
    | Obj(t, r) -> "{" ^ (term_to_string t) ^ "}" ^ (nstars r)
    | Arrow(a,b) -> (lppterm_to_string a) ^ " -> " ^ (lppterm_to_string b)
    | Forall(ts, t) ->
        "forall " ^ (bindings_to_string ts) ^ ", " ^ (lppterm_to_string t)


  
    
