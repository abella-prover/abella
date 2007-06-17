open Term

(* Basic operations *)

type elt = term
type t = elt list

let empty : t = []

let rec mem elt ctx =
  match ctx with
    | [] -> false
    | head::tail -> eq elt head || mem elt tail

let add elt ctx = ctx @ [elt]

let is_empty ctx = ctx = []

let element_to_string elt =
  Pprint.term_to_string elt

let context_to_string ctx =
  let rec aux lst =
    match lst with
      | [] -> ""
      | [last] -> element_to_string last
      | head::tail -> (element_to_string head) ^ ", " ^ (aux tail)
  in
    aux ctx

let subcontext ctx1 ctx2 =
  List.for_all (fun elt -> List.mem elt ctx2) ctx1

let union ctx1 ctx2 =
  ctx1 @ ctx2

let exists f ctx = List.exists f ctx

let map f ctx = List.map f ctx
