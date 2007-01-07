open Term
open Pprint

type lppterm =
  | Obj of term
  | Arrow of lppterm * lppterm
  | Forall of (term * term) list * lppterm

let binding_to_string (tm, ty) =
  "(" ^ (term_to_string tm) ^ " : " ^ (term_to_string ty) ^ ")"

let bindings_to_string ts =
  String.concat " " (List.map binding_to_string ts)
    
let rec lppterm_to_string t =
  match t with
    | Obj(t) -> "{" ^ (term_to_string t) ^ "}"
    | Arrow(a,b) -> (lppterm_to_string a) ^ " -> " ^ (lppterm_to_string b)
    | Forall(ts, t) ->
        "forall " ^ (bindings_to_string ts) ^ ", " ^ (lppterm_to_string t)


  
    
