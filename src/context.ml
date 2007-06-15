open Term

type element =
  | Term of Term.term
  | Var of Term.var

let var name = Var {name = name; ts = 0; tag = Eigen}
let term t = Term t
  
let is_term t =
  match t with
    | Term _ -> true
    | _ -> false
        
let is_var t =
  match t with
    | Var _ -> true
    | _ -> false
  
(* Basic operations *)

type t = element list

let empty : element list = []

let mem elt ctx = List.mem elt ctx

let add elt ctx = elt::ctx

let is_empty ctx = ctx = []

let element_to_string elt =
  match elt with
    | Term t -> Pprint.term_to_string t
    | Var v -> v.name

let context_to_string ctx =
  let vars = List.filter is_var ctx in
  let terms = List.filter is_term ctx in
  let rec aux lst =
    match lst with
      | [last] -> element_to_string last
      | head::tail -> (element_to_string head) ^ ", " ^ (aux tail)
      | [] -> ""
  in
    aux (vars @ terms)

(* Helper operations *)

let add_term term ctx = add (Term(term)) ctx
  
let mem_term term ctx = mem (Term(term)) ctx

