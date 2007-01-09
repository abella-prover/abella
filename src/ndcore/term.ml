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

type tag = Eigen | Constant | Logic
type id = string
type var = {
  name : id  ;
  tag  : tag ;
  ts   : int ; (* Always zero for constants in Bedwyr *)
  lts  : int
}

type term = rawterm
and rawterm =
  | Var  of var
  | DB   of int
  | NB   of int (* Nabla variables *)
  | Lam  of int * term
  | App  of term * term list
  | Susp of term * int * int * env
  | Ptr  of ptr
and ptr = in_ptr ref
and in_ptr = V of var | T of term
and env = envitem list
and envitem = Dum of int | Binding of term * int

exception NonNormalTerm
exception NotValidTerm

(* Fast structural equality modulo Ptr -- no normalization peformed. *)
let rec eq t1 t2 =
  match t1,t2 with
    (* Compare leafs *)
    | DB i1, DB i2
    | NB i1, NB i2 -> i1=i2
    | Ptr {contents=V v1}, Ptr {contents=V v2} -> v1=v2
    (* Ignore Ptr. It's an implementation artifact *)
    | _, Ptr {contents=T t2} -> eq t1 t2
    | Ptr {contents=T t1}, _ -> eq t1 t2
    (* Propagation *)
    | App (h1,l1), App (h2,l2) ->
        List.length l1 = List.length l2 &&
        List.fold_left2
          (fun test t1 t2 -> test && eq t1 t2)
          true (h1::l1) (h2::l2)
    | Lam (n,t1), Lam (m,t2) -> n = m && eq t1 t2
    | Var _, _ | _, Var _ -> assert false
    | Susp (t,ol,nl,e), Susp (tt,oll,nll,ee) ->
        ol = oll && nl = nll && eq t tt &&
          List.fold_left2
            (fun test e1 e2 ->
               test && match e1,e2 with
                 | Dum i, Dum j when i = j -> true
                 | Binding (t,i), Binding (tt,j) when i=j && eq t tt -> true
                 | _ -> false)
            true e ee
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

type bind_state = int
let bind_stack = Stack.create ()
let bind_len = ref 0

let where () = Printf.printf "#%d\n" !bind_len

let save_state () = !bind_len

let restore_state n =
  assert (n <= !bind_len) ;
  for i = 1 to !bind_len-n do
    let (v,contents) = Stack.pop bind_stack in
      v := contents
  done ;
  bind_len := n

type subst = (ptr*in_ptr) list
type unsubst = subst

let bind v t =
  let dv = getref (deref v) in
  let dt = deref t in
    if match dt with Ptr r when r==dv -> false | _ -> true then begin
      Stack.push (dv,!dv) bind_stack ;
      dv := T dt ;
      incr bind_len
    end

exception Done

let get_subst state =
  let subst = ref [] in
  let count = ref (!bind_len-state) in
    assert (!count >= 0) ;
    try
      Stack.iter
        (fun (v,old) ->
           if !count = 0 then raise Done ;
           subst := (v,!v)::!subst ;
           decr count)
        bind_stack ;
      !subst
    with Done -> !subst

let apply_subst s = List.fold_left (fun sub (v,contents) ->
                                      let old = !v in
                                        v := contents ;
                                        (v,old)::sub) [] s
let undo_subst = List.iter (fun (s,old) -> s:=old)

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

(** We try to attach useful names to generated variables.
  * For that purpose we use prefixes like 'h' or 'x',
  * freshness is ensured by the suffix. During parsing, one must take care
  * to rename variables that could conflict with generated ones.
  * TODO choose a policy here.. use more prefixes depending on the type,
  * if typing is introduced ? *)

let prefix = function
  | Constant -> "c"
  | Logic -> "H"
  | Eigen -> "h"

let getAbsName () = "x"

(** Generating a fresh variable with a given time stamp; the use of ref
  * ensures uniqueness. We should attach useful names as well, but this 
  * will do for the moment. 
  * I hide [varcount] cause resetting it hurts the consistency of the system. *)
let fresh =
  let varcount = ref 0 in
    fun () ->
      let i = !varcount in
        incr varcount ;
        i

let fresh ?(name="") ?(tag=Logic) ?(lts=0) ts =
  let i = fresh () in
  let name = if name = "" then (prefix tag) ^ (string_of_int i) else name in
    Ptr (ref (V { name=name ; ts=ts ; lts=lts ; tag=tag }))

(* Recursively raise dB indices and abstract over variables
 * selected by [test]. *)
let abstract test =
  let rec aux n t = match t with
    | NB i -> t
    | DB i -> if i>=n then DB (i+1) else t
    | App (h,ts) ->
        App ((aux n h), (List.map (aux n) ts))
    | Lam (m,s) -> Lam (m, aux (n+m) s)
    | Ptr {contents=T t} -> Ptr (ref (T (aux n t)))
    | Ptr {contents=V v} -> if test t v.name then DB n else t
    | Var _ -> assert false
    | Susp _ -> raise NonNormalTerm
  in aux

(** Abstract [t] over term [v]. *)
let abstract_var v t = lambda 1 (abstract (fun t id' -> t = v) 1 t)

(** Abstract [t] over constant or variable named [id]. *)
let abstract id t = lambda 1 (abstract (fun t id' -> id' = id) 1 t)

(** Logic variables of [ts], assuming that it is normalized. *)
  
let find_vars ?(tag=Logic) ts =
  let rec fv l t = match observe t with
    | Var v ->
        if v.tag = tag && not (List.mem t l) then (t::l) else l
    | App (h,ts) -> List.fold_left fv (fv l h) ts
    | Lam (n,t') -> fv l t'
    | NB _ | DB _ -> l
    | Susp _ -> assert false
    | Ptr _ -> assert false
  in
    List.fold_left fv [] ts
      
let logic_vars = find_vars ~tag:Logic

(** Utilities.
  * Easy creation of constants and variables, with sharing. *)

let const ?(tag=Constant) ?(lts=0) s n =
  Ptr (ref (V { name=s; ts=n; lts=lts; tag=tag }))
let var ?(tag=Logic) ?(lts=0) s n =
  Ptr (ref (V { name=s; ts=n; lts=lts; tag=tag }))

let tbl = Hashtbl.create 100
let reset_namespace () = Hashtbl.clear tbl
let reset_namespace_vars () =
  Hashtbl.iter
    (fun k v -> match v with
       | Ptr {contents=V {tag=Logic}} -> Hashtbl.remove tbl k
       | _ -> ())
    tbl

let atom ?(tag=Logic) ?(ts=0) name =
  try
    Hashtbl.find tbl name
  with
    | Not_found ->
        assert (name <> "") ;
        let t =
          match name.[0] with
            | 'A'..'Z' -> var ~tag:tag name ts
            | _ -> const name ts
        in
          Hashtbl.add tbl name t ;
          t

let string text = const text 0

let binop s a b = App ((atom s),[a;b])

let rec collapse_lam t = match t with
  | Lam (n,t') ->
      begin match collapse_lam t' with 
        | Lam (m,u) -> Lam (n+m,u)
        | _ -> t
      end
  | _ -> t

let db n = DB n
let nabla n = NB n

(* let app a b = if b = [] then a else ref (App (a,b)) *)
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
