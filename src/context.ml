open Term

(* Basic operations *)

type elt = term
type t = elt list

let empty : t = []

let size ctx = List.length ctx

let rec mem elt ctx =
  match ctx with
    | [] -> false
    | head::tail -> eq elt head || mem elt tail

let rec remove elt ctx =
  match ctx with
    | [] -> []
    | head::tail when eq elt head -> remove elt tail
    | head::tail -> head::(remove elt tail)

let rec xor ctx1 ctx2 =
  match ctx1 with
    | [] -> ([], ctx2)
    | head::tail ->
        if mem head ctx2
        then xor tail (remove head ctx2)
        else let ctx1', ctx2' = xor tail ctx2 in
          (head::ctx1', ctx2')
        
let add elt ctx = ctx @ [elt]

let is_empty ctx = ctx = []

let element_to_string elt =
  term_to_string elt

let context_to_string ctx =
  let rec aux lst =
    match lst with
      | [] -> ""
      | [last] -> element_to_string last
      | head::tail -> (element_to_string head) ^ ", " ^ (aux tail)
  in
    aux ctx

let subcontext ctx1 ctx2 =
  List.for_all (fun elt -> mem elt ctx2) ctx1

let union ctx1 ctx2 =
  ctx1 @ ctx2

let union_list ctx_list =
  List.fold_left union empty ctx_list

let exists f ctx = List.exists f ctx

let map f ctx = List.map f ctx

let rec assoc t pair_list =
  match pair_list with
    | [] -> []
    | (a, b)::tail when eq t a -> b::(assoc t tail)
    | head::tail -> assoc t tail

let rec remove_assoc t pair_list =
  match pair_list with
    | [] -> []
    | (a, b)::tail when eq t a -> remove_assoc t tail
    | head::tail -> head::(remove_assoc t tail)
  
let rec group pair_list =
  match pair_list with
    | [] -> []
    | (a, b)::_ ->
        let pairings = assoc a pair_list in
        let pair_list' = remove_assoc a pair_list in
          (a, pairings)::(group pair_list')

let context_to_list ctx = ctx
            
let cons = const "::"
            
let context_to_term ctx =
  let rec aux ctx =
    match ctx with
      | [] -> const "nil"
      | [last] when is_eigen last -> last
      | head::tail -> app cons [head; aux tail]
  in
    aux (List.rev ctx)

let is_cons t =
  match observe t with
    | App(c, [_; _]) when c = cons -> true
    | _ -> false

let extract_cons t =
  match observe t with
    | App(_, [a; b]) -> (a, b)
    | _ -> assert false
      
let normalize ctx =
  let rec remove_dups ctx =
    match ctx with
      | [] -> []
      | head::tail -> head::(remove_dups (remove head tail))
  in
  let rec remove_cons ctx =
    match ctx with
      | [] -> []
      | head::tail when is_cons head ->
          let a, b = extract_cons head in
            remove_cons (b::a::tail)
      | head::tail -> head::(remove_cons tail)
  in
    remove_dups (remove_cons ctx)

let extract_singleton ctx =
  match ctx with
    | [e] -> e
    | _ -> failwith "Non-singleton context encountered"

let reconcile pair_list =
  let pair_list = List.filter (fun (x,y) -> not (is_empty x)) pair_list in
  let pair_list = List.map (fun (x,y) -> xor x y) pair_list in
  let var_ctx_list = List.map
    (fun (x,y) -> (extract_singleton x, y)) pair_list
  in
  let groups = group var_ctx_list in
  let groups = List.map (fun (x,y) -> (x, union_list y)) groups in
  let groups = List.map (fun (x,y) -> (x, normalize y)) groups in
    List.iter (fun (var, ctx) ->
                 Unify.right_unify var (context_to_term ctx)) groups
