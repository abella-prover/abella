(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006 Nadathur, Linnell, Baelde, Ziegler                    *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with this code; if not, write to the Free Software Foundation,     *)
(* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA             *)
(****************************************************************************)

open Extensions

type tag = Eigen | Constant | Logic | Nominal
type id = string
type var = {
  name : id ;
  tag  : tag    ;
  ts   : int
}

type term = rawterm
and rawterm =
  | Var  of var
  | DB   of int
  | Lam  of int * term
  | App  of term * term list
  | Susp of term * int * int * env
  | Ptr  of ptr
and ptr = in_ptr ref
and in_ptr = V of var | T of term
and env = envitem list
and envitem = Dum of int | Binding of term * int

(* Fast structural equality modulo Ptr -- no normalization peformed. *)
let rec eq t1 t2 =
  match t1,t2 with
    (* Compare leafs *)
    | DB i1, DB i2 -> i1=i2
    | Ptr {contents=V v1}, Ptr {contents=V v2} ->
        (v1.tag = Nominal && v2.tag = Nominal && v1.name = v2.name) ||
          v1=v2
    (* Ignore Ptr. It's an implementation artifact *)
    | _, Ptr {contents=T t2} -> eq t1 t2
    | Ptr {contents=T t1}, _ -> eq t1 t2
    (* Propagation *)
    | App (h1,l1), App (h2,l2) ->
        List.length l1 = List.length l2 &&
        List.for_all2 eq (h1::l1) (h2::l2)
    | Lam (n,t1), Lam (m,t2) -> n = m && eq t1 t2
    | Var _, _ | _, Var _ -> assert false
    | Susp (t1,ol1,nl1,e1), Susp (t2,ol2,nl2,e2) ->
        ol1 = ol2 && nl1 = nl2 && eq t1 t2 &&
          List.for_all2
            (fun et1 et2 ->
               match et1,et2 with
                 | Dum i, Dum j -> i = j
                 | Binding (t1,i), Binding (t2,j) -> i=j && eq t1 t2
                 | _ -> false)
          e1 e2
    | _ -> false

let rec observe = function
  | Ptr {contents=T d} -> observe d
  | Ptr {contents=V v} -> Var v
  | t -> t

let rec deref = function
  | Ptr {contents=T t} -> deref t
  | t -> t

let getref = function
  | Ptr t -> t
  | _ -> assert false

(* Binding a variable to a term. The *contents* of the cell representing the
 * variable is a reference which must be updated. Also the variable must
 * not be made a reference to itself. This can be changed to mimic the
 * Prolog representation of bound variables but then deref will have to
 * work differently. This is the place to introduce trailing. *)

let bind_stack = Stack.create ()

let bind v t =
  let dv = getref (deref v) in
  let dt = deref t in
    if match dt with Ptr r when r==dv -> false | _ -> true then begin
      Stack.push (dv,!dv) bind_stack ;
      dv := T dt
    end

let prefix = function
  | Constant -> "c"
  | Logic -> "?"
  | Eigen -> "_"
  | Nominal -> "n"

type bind_state = (term * term) list
    
let get_bind_state () =
  let state = ref [] in
    Stack.iter
      (fun (v, _) ->
         state := (Ptr v, Ptr (ref !v))::!state)
      bind_stack ;
    !state

let clear_bind_state () =
  Stack.iter (fun (v, value) -> v := value) bind_stack ;
  Stack.clear bind_stack

let set_bind_state state =
  clear_bind_state () ;
  List.iter (fun (v, value) -> bind v value) state

(* Raise the substitution *)
let rec add_dummies env n m = 
  match n with
    | 0 -> env
    | _ -> let n'= n-1 in ((Dum (m+n'))::(add_dummies env n' m))

(* Add [n] abstractions. *)
let rec lambda n t =
  let t = deref t in
    if n = 0 then t else
      match t with
        | Lam (n',t') -> lambda (n+n') t'
        | _ -> Lam (n,t)

(* Recursively raise dB indices and abstract over variables
 * selected by [test]. *)
let abstract test =
  let rec aux n t = match t with
    | DB i -> t
    | App (h,ts) ->
        App ((aux n h), (List.map (aux n) ts))
    | Lam (m,s) -> Lam (m, aux (n+m) s)
    | Ptr {contents=T t} -> Ptr (ref (T (aux n t)))
    | Ptr {contents=V v} -> if test t v.name then DB n else t
    | Var _ -> assert false
    | Susp _ -> assert false
  in aux

(** Abstract [t] over term [v]. *)
let abstract_var v t = lambda 1 (abstract (fun t id' -> t = v) 1 t)

(** Abstract [t] over constant or variable named [id]. *)
let abstract id t = lambda 1 (abstract (fun t id' -> id' = id) 1 t)

(** Utilities.
  * Easy creation of constants and variables, with sharing. *)

let nominal_var name = Ptr (ref (V {name=name; ts=max_int; tag=Nominal}))
  
let var tag name ts =
  if tag = Nominal then
    nominal_var name
  else
    Ptr (ref (V { name=name ; ts=ts ; tag=tag }))

let db n = DB n
let app a b = if b = [] then a else match observe a with
  | App(a,c) -> App (a,c @ b)
  | _ -> App (a,b)
let susp t ol nl e = Susp (t,ol,nl,e)

module Notations =
struct
  let (%=) = eq
  let (!!) = observe
  let (//) = lambda
  let (^^) = app
end

(** LPP specific changes *)

let const ?(ts=0) s = Ptr (ref (V { name=s ; ts=ts ; tag=Constant }))
  
let fresh =
  let varcount = ref 0 in
    fun () ->
      let i = !varcount in
        incr varcount ;
        i
      
let fresh ?(tag=Logic) ts =
  let i = fresh () in
  let name = (prefix tag) ^ (string_of_int i) in
    var tag name ts

let fresh_name name used =
  let rec aux name =
    if List.mem_assoc name used then
      aux (name ^ "'")
    else
      name
  in
    aux name
      
let fresh_wrt tag name used =
  let name = fresh_name name used in
  let v = var tag name 0 in
    (v, (name, v)::used)

let binop s a b = App ((const s),[a;b])
            
let find_vars tag ts =
  let rec fv l t = match observe t with
    | Var v ->
        if v.tag = tag && not (List.mem v l) then v::l else l
    | App (h,ts) -> List.fold_left fv (fv l h) ts
    | Lam (n,t') -> fv l t'
    | DB _ -> l
    | Susp _ -> assert false
    | Ptr _ -> assert false
  in
    List.fold_left fv [] ts

let map_vars f t =
  let rec aux t =
    match observe t with
      | Var(v) -> [f v]
      | DB _ -> []
      | Lam(i, t) -> aux t
      | App(t, ts) -> List.append (aux t) (List.flatten (List.map aux ts))
      | Susp _ -> failwith "map_vars called on non-normal term"
      | Ptr _ -> assert false
  in
    aux t

let map_vars_list f ts =
  List.flatten (List.map (map_vars f) ts)

let term_to_var t =
  match observe t with
    | Var v -> v
    | _ -> failwith "term_to_var called on non-var"

let is_eigen t =
  match observe t with
    | Var v -> v.tag = Eigen
    | _ -> false

(* Normalization *)

(** Make an environment appropriate to [n] lambda abstractions applied to
    the arguments in [args]. Return the environment together with any
    remaining lambda abstractions and arguments. (There can not be both
    abstractions and arguments left over). *)
let make_env n args =
  let rec aux n args e =
    if n = 0 || args = []
    then (e, n, args)
    else aux (n-1) (List.tl args) (Binding(List.hd args, 0)::e)
  in aux n args []
        
(** Head normalization function.*)
let rec hnorm term =
  match observe term with
    | Var _
    | DB _ -> term
    | Lam(n,t) -> lambda n (hnorm t)
    | App(t,args) ->
        let t = hnorm t in
          begin match observe t with
            | Lam(n,t) ->
                let e, n', args' = make_env n args in
                let ol = List.length e in
                  if n' > 0
                  then hnorm (susp (lambda n' t) ol 0 e)
                  else hnorm (app (susp t ol 0 e) args')
            | _ -> app t args
          end
    | Susp(t,ol,nl,e) ->
        let t = hnorm t in
          begin match observe t with
            | Var _ -> t
            | DB i ->
                if i > ol then
                  (* The index points to something outside the suspension *)
                  db (i-ol+nl)
                else
                  (* The index has to be substituted for [e]'s [i]th element *)
                  begin match List.nth e (i-1) with
                    | Dum l -> db (nl - l)
                    | Binding (t,l) -> hnorm (susp t 0 (nl-l) [])
                  end
            | Lam(n,t) ->
                lambda n (hnorm (susp t (ol+n) (nl+n)
                                       (add_dummies e n nl)))
            | App(t,args) ->
                let wrap x = susp x ol nl e in
                  hnorm (app (wrap t) (List.map wrap args))
            | Susp _ -> hnorm (susp (hnorm t) ol nl e)
            | Ptr _ -> assert false
          end
    | Ptr _ -> assert false

let rec deep_norm t =
  let t = hnorm t in
    match observe t with
      | Var _ | DB _ -> t
      | Lam (n,t) -> lambda n (deep_norm t)
      | App (a,b) ->
            begin match observe a with
              | Var _ | DB _ ->
                    app a (List.map deep_norm b)
              | _ -> deep_norm (app (deep_norm a) (List.map deep_norm b))
            end
      | Ptr _ | Susp _ -> assert false
          
(* Pretty printing *)

exception Found of int

type assoc = Left | Right | Both | No
  
(* List of infix operators sorted by priority, low to high. *)
let infix : (string * assoc) list =
  [("=>", Right); ("::", Right); ("=", No)]

let is_infix x = List.mem_assoc x infix
let get_assoc op = List.assoc op infix
let priority x =
  try
    ignore (List.fold_left
              (fun i (e, assoc) -> if e = x then raise (Found i) else i+1)
              1 infix) ;
    0
  with
    | Found i -> i
let get_max_priority () = List.length infix

let is_obj_quantifier x = x = "pi" || x = "sigma"

let tag2str = function
  | Constant -> "c"
  | Eigen -> "e"
  | Logic -> "l"
  | Nominal -> "n"

let parenthesis x = "(" ^ x ^ ")"

let rec list_range a b =
  if a > b then [] else a::(list_range (a+1) b)

let abs_name = "x"
    
let term_to_string term =
  let term = deep_norm term in
  let high_pr = 2 + get_max_priority () in
  let pp_var x = abs_name ^ (string_of_int x) in
  let rec pp pr n term =
    match observe term with
      | Var v -> v.name
          (* ^ ":" ^ (tag2str v.tag) *)
          (* ^ ":" ^ (string_of_int v.ts) *) 
      | DB i -> pp_var (n-i+1)
      | App (t,ts) ->
          begin match observe t, ts with
            | Var {name=op; tag=Constant}, [a; b] when is_infix op ->
                let op_p = priority op in
                let assoc = get_assoc op in
                let pr_left, pr_right = begin match assoc with
                  | Left -> op_p, op_p+1
                  | Right -> op_p+1, op_p
                  | _ -> op_p, op_p
                  end in
                let res =
                  (pp pr_left n a) ^ " " ^ op ^ " " ^ (pp pr_right n b)
                in
                  if op_p >= pr then res else parenthesis res
            | Var {name=op; tag=Constant}, [a] when is_obj_quantifier op ->
                let res = op ^ " " ^ (pp 0 n a) in
                  if pr < high_pr then res else parenthesis res
            | _ ->
                let res =
                  String.concat " " (List.map (pp high_pr n) (t::ts))
                in
                  if pr < high_pr then res else parenthesis res
          end
      | Lam (0,t) -> assert false
      | Lam (i,t) ->
          let res = ((String.concat "\\"
                       (List.map pp_var (list_range (n+1) (n+i)))) ^ "\\" ^
                      (pp 0 (n+i) t)) in
            if pr == 0 then res else parenthesis res
      | Ptr t -> assert false (* observe *)
      | Susp _ -> assert false (* deep_norm *)
  in
    pp 0 0 term

let full_eq t1 t2 = eq (deep_norm t1) (deep_norm t2)

let get_used ts =
  let rec aux t =
    match deref (hnorm t) with
      | DB i -> []
      | Lam(n, t) -> aux t
      | App(t, ts) -> (aux t) @ (List.flatten (List.map aux ts))
      | Ptr {contents=V v} -> [(v.name, t)]
      | _ -> assert false
  in
    List.unique (List.flatten (List.map aux ts))

let is_free t =
  match t with
    | Ptr {contents=V _} -> true
    | Ptr {contents=T _} -> false
    | _ -> assert false

let find_var_refs tag ts =
  let rec fv l t = match t with
    | Var _ -> assert false
    | App (h, ts) -> List.fold_left fv (fv l h) ts
    | Lam (n, t') -> fv l t'
    | DB _ -> l
    | Susp _ -> assert false
    | Ptr {contents=T t'} -> fv l t'
    | Ptr {contents=V v} ->
        if v.tag = tag && not (List.mem t l) then t::l else l
  in
    List.fold_left fv [] (List.map deep_norm ts)
