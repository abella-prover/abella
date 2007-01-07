open Term
open Pprint

type restriction = int * bool

type lppterm =
  | Obj of term * restriction
  | Arrow of lppterm * lppterm
  | Forall of (term * term) list * lppterm

let obj t = Obj(t, (0, false))
let arrow a b = Arrow(a, b)
let forall ts t = Forall(ts, t)

let inactive_obj t r = Obj(t, (r, false))
let active_obj t r = Obj(t, (r, true))

let restriction_to_string (n, active) =
  if active then String.make n '*' else ""

let binding_to_string (tm, ty) =
  "(" ^ (term_to_string tm) ^ " : " ^ (term_to_string ty) ^ ")"

let bindings_to_string ts =
  String.concat " " (List.map binding_to_string ts)

let rec lppterm_to_string t =
  match t with
    | Obj(t, r) -> "{" ^ (term_to_string t) ^ "}" ^
        (restriction_to_string r)
    | Arrow(a,b) -> (lppterm_to_string a) ^ " -> " ^ (lppterm_to_string b)
    | Forall(ts, t) ->
        "forall " ^ (bindings_to_string ts) ^ ", " ^ (lppterm_to_string t)

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

  
    
