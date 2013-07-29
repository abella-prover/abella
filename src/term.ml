(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006-2009 Nadathur, Linnell, Baelde, Ziegler, Gacek        *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

open Extensions

type ty = Ty of ty list * string

type tag = Eigen | Constant | Logic | Nominal
type id = string
type var = {
  name : id ;
  tag  : tag ;
  ts   : int ;
  ty   : ty ;
}

type tyctx = (id * ty) list

type term = rawterm
and rawterm =
  | Var  of var
  | DB   of int
  | Lam  of tyctx * term
  | App  of term * term list
  | Susp of term * int * int * env
  | Ptr  of ptr
and ptr = in_ptr ref
and in_ptr = V of var | T of term
and env = envitem list
and envitem = Dum of int | Binding of term * int

(* Utilities for constructing and deconstructing terms *)

let rec observe = function
  | Ptr {contents=T d} -> observe d
  | Ptr {contents=V v} -> Var v
  | t -> t

let db n = DB n

let get_ctx_tys tyctx = List.map snd tyctx

let rec lambda idtys t =
  if idtys = [] then t else
    match t with
      | Lam (idtys',t') -> lambda (idtys @ idtys') t'
      | _ -> Lam (idtys,t)

let app a b =
  if b = [] then
    a
  else
    match observe a with
      | App(a,c) -> App (a,c @ b)
      | _ -> App (a,b)

let susp t ol nl e = Susp (t,ol,nl,e)


(* Normalization and Equality *)

(* Raise the substitution *)
let rec add_dummies env n m =
  match n with
    | 0 -> env
    | _ -> let n'= n-1 in ((Dum (m+n'))::(add_dummies env n' m))

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
    | Lam(idtys,t) -> lambda idtys (hnorm t)
    | App(t,args) ->
        let t = hnorm t in
          begin match observe t with
            | Lam(idtys,t) ->
                let n = List.length idtys in
                let e, n', args' = make_env n args in
                let ol = List.length e in
                  if n' > 0
                  then hnorm (susp (lambda (List.drop (n-n') idtys) t) ol 0 e)
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
            | Lam(idtys,t) ->
                let n = List.length idtys in
                  lambda idtys (hnorm (susp t (ol+n) (nl+n) (add_dummies e n nl)))
            | App(t,args) ->
                let wrap x = susp x ol nl e in
                  hnorm (app (wrap t) (List.map wrap args))
            | Susp _ -> assert false
            | Ptr _ -> assert false
          end
    | Ptr _ -> assert false

let rec eq t1 t2 =
  match observe (hnorm t1), observe (hnorm t2) with
    | DB i1, DB i2 -> i1 = i2
    | Var v1, Var v2 -> v1 = v2
    | App(h1,l1), App(h2,l2) ->
        List.length l1 = List.length l2 &&
        List.for_all2 eq (h1::l1) (h2::l2)
    | Lam(idtys1,t1), Lam(idtys2,t2) ->
        (get_ctx_tys idtys1) = (get_ctx_tys idtys2) && eq t1 t2
    | _ -> false

(* Binding a variable to a term. The *contents* of the cell representing the
 * variable is a reference which must be updated. Also the variable must
 * not be made a reference to itself. *)

(* bind_state is a list of (var, old_value, new_value) *)
type bind_state = (ptr * in_ptr * term) list
let bind_state : bind_state ref = ref []
let bind_len = ref 0

let rec deref = function
  | Ptr {contents=T t} -> deref t
  | t -> t

let getref = function
  | Ptr t -> t
  | _ -> assert false

let bind v t =
  let dv = getref (deref v) in
  let dt = deref t in
    assert (match dt with Ptr r -> dv != r | _ -> true) ;
    bind_state := (dv, !dv, dt) :: !bind_state ;
    incr bind_len ;
    dv := T dt

let get_bind_state () = !bind_state

let clear_bind_state () =
  List.iter (fun (v, ov, nv) -> v := ov) !bind_state ;
  bind_state := [] ;
  bind_len := 0

let set_bind_state state =
  clear_bind_state () ;
  List.iter (fun (v, ov, nv) -> bind (Ptr v) nv) (List.rev state)


(* Scoped bind state is more efficient than regular bind state, but it
   must always be used in a lexically scoped fashion. The unwind_state
   wraps a function with a scoped get and set. *)

type scoped_bind_state = int

let get_scoped_bind_state () = !bind_len

let set_scoped_bind_state state =
  while !bind_len > state do
    match !bind_state with
      | (v, ov, nv)::rest ->
          v := ov ;
          bind_state := rest ;
          decr bind_len
      | [] -> assert false
  done

let unwind_state f x =
  let state = get_scoped_bind_state () in
  let result = f x in
  set_scoped_bind_state state ;
  result

(* Recursively raise dB indices and abstract over variables
 * selected by [test]. *)
let abstract test =
  let rec aux n t = match t with
    | DB i -> t
    | App(h,ts) -> App(aux n h, List.map (aux n) ts)
    | Lam(idtys,s) -> Lam (idtys, aux (n + List.length idtys) s)
    | Ptr {contents=T t} -> Ptr (ref (T (aux n t)))
    | Ptr {contents=V v} -> if test t v.name then DB n else t
    | Var _ -> assert false
    | Susp _ -> assert false
  in aux

(** Abstract [t] over constant or variable named [id]. *)
let abstract id ty t =
  lambda [(id,ty)] (abstract (fun t id' -> id' = id) 1 t)

(** Utilities.
  * Easy creation of constants and variables, with sharing. *)

let nominal_var name ty =
  Ptr (ref (V {name=name; ts=max_int; tag=Nominal; ty=ty}))

let var tag name ts ty =
  if tag = Nominal then
    nominal_var name ty
  else
    Ptr (ref (V { name=name ; ts=ts ; tag=tag ; ty=ty }))

let const ?(ts=0) s ty =
  Ptr (ref (V { name=s ; ts=ts ; tag=Constant ; ty=ty}))

module Notations =
struct
  let (//) = lambda
  let (^^) = app
end


let prefix = function
  | Constant -> "c"
  | Logic -> "?"
  | Eigen -> "_"
  | Nominal -> "n"

let fresh =
  let varcount = ref 1 in
    fun () ->
      let i = !varcount in
        incr varcount ;
        i

let fresh ?(tag=Logic) ts ty =
  let i = fresh () in
  let name = (prefix tag) ^ (string_of_int i) in
    var tag name ts ty

let remove_trailing_numbers s =
  Str.global_replace (Str.regexp "[0-9]*$") "" s

let fresh_name name used =
  let basename = remove_trailing_numbers name in
  let rec aux i =
    let name = basename ^ (string_of_int i) in
      if List.mem_assoc name used then
        aux (i+1)
      else
        name
  in
    (* Try to avoid any renaming *)
    if List.mem_assoc name used then
      aux 1
    else
      name

let fresh_wrt ~ts tag name ty used =
  let name = fresh_name name used in
  let v = var tag name ts ty in
    (v, (name, v)::used)

let term_to_var t =
  match observe (hnorm t) with
    | Var v -> v
    | _ -> assert false

(* Select all variable references which satisfy f *)
let select_var_refs f ts =
  let rec fv acc t =
    let t = hnorm t in
      match observe t with
        | Var v -> if f v then t::acc else acc
        | App (h, ts) -> List.fold_left fv (fv acc h) ts
        | Lam (idtys, t') -> fv acc t'
        | DB _ -> acc
        | Susp _ -> assert false
        | Ptr _ -> assert false
  in
    List.fold_left fv [] ts

let find_var_refs tag ts =
  List.unique (select_var_refs (fun v -> v.tag = tag) ts)

let find_vars tag ts =
  List.map term_to_var (find_var_refs tag ts)

let map_vars f ts =
  select_var_refs (fun v -> true) ts
  |> List.rev
  |> List.unique
  |> List.map term_to_var
  |> List.map f

let get_used ts =
  select_var_refs (fun v -> true) ts
  |> List.rev
  |> List.unique
  |> List.map (fun t -> ((term_to_var t).name, t))

(* Pretty printing *)

exception Found of int

type assoc = Left | Right | Both | No

(* List of infix operators sorted by priority, low to high. *)
let infix : (string * assoc) list =
  [("=>", Right); ("::", Right)]

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

let is_lam t =
  match observe (hnorm t) with
    | Lam _ -> true
    | _ -> false

let tag2str = function
  | Constant -> "c"
  | Eigen -> "e"
  | Logic -> "l"
  | Nominal -> "n"

let parenthesis x = "(" ^ x ^ ")"

let rec list_range a b =
  if a > b then [] else a::(list_range (a+1) b)

let abs_name = "x"

let ty_to_string ty =
  let rec aux nested ty =
    match ty with
      | Ty([], bty) -> bty
      | Ty(tys, bty) ->
          let res = String.concat " -> "(List.map (aux true) tys @ [bty]) in
            if nested then parenthesis res else res
  in
    aux false ty

let term_to_string term =
  let high_pr = 2 + get_max_priority () in
  let pp_var x = abs_name ^ (string_of_int x) in
(*   let pp_var_ty x ty = (pp_var x) ^ ":" ^ (ty_to_string ty) in *)
  let rec pp cx pr n term =
    match observe (hnorm term) with
      | Var v -> v.name
          (* ^ ":" ^ (tag2str v.tag) *)
          (* ^ ":" ^ (string_of_int v.ts) *)
          (* ^ ":" ^ (ty_to_string v.ty) *)
      | DB i -> 
          (try List.nth cx (i - 1) with _ -> pp_var (n - i + 1))
      | App (t,ts) ->
          begin match observe (hnorm t), ts with
            | Var {name=op; tag=Constant; ts=ts; ty=ty}, [a; b] when is_infix op ->
                let op_p = priority op in
                let assoc = get_assoc op in
                let pr_left, pr_right = begin match assoc with
                  | Left -> op_p, op_p+1
                  | Right -> op_p+1, op_p
                  | _ -> op_p, op_p
                  end in
                let res =
                  (pp cx pr_left n a) ^ " " ^ op ^ " " ^ (pp cx pr_right n b)
                in
                  if op_p >= pr then res else parenthesis res
            | Var {name=op; tag=Constant; ts=ts; ty=ty}, [a] when
                is_obj_quantifier op && is_lam a ->
                let res = op ^ " " ^ (pp cx 0 n a) in
                  if pr < high_pr then res else parenthesis res
            | _ ->
                let res =
                  String.concat " " (List.map (pp cx high_pr n) (t::ts))
                in
                  if pr < high_pr then res else parenthesis res
          end
      | Lam ([],t) -> assert false
      | Lam (tycx,t) ->
          let i = List.length tycx in
          let default_vars = List.map pp_var (list_range (n + 1) (n + i)) in
          let vars = List.map2 begin
            fun (hv, _) dv -> match hv with
            | "_" -> dv
            | _ -> hv
          end tycx default_vars in
          let tcx = List.rev_append vars cx in
          let res = ((String.concat "\\" vars) ^ "\\" ^
                      (pp tcx 0 (n+i) t)) in
          if pr == 0 then res else parenthesis res
      | Ptr t -> assert false (* observe *)
      | Susp _ -> assert false (* hnorm *)
  in
    pp [] 0 0 term

let term_to_name t =
  (term_to_var t).name

let term_to_pair t =
  (term_to_name t, t)

let is_free t =
  match t with
    | Ptr {contents=V _} -> true
    | Ptr {contents=T _} -> false
    | _ -> assert false

let is_nominal t =
  match observe (hnorm t) with
    | Var {tag=Nominal; name=name; ts=ts; ty=ty} -> true
    | _ -> false

let term_head_var t =
  let rec aux t =
    let t = hnorm t in
      match t with
        | Ptr {contents=T t} -> aux t
        | Ptr {contents=V v} -> Some t
        | App(t, ts) -> aux t
        | _ -> None
  in
    aux t

let term_head_name t =
  match term_head_var t with
    | Some t -> term_to_name t
    | None -> assert false

let is_head_name name t =
  match term_head_var t with
    | Some (Ptr {contents=V v}) when v.name = name -> true
    | _ -> false

let extract_tids test terms =
  terms
  |> map_vars (fun v -> (v.name, v.ty))
  |> List.find_all (fun (id, ty) -> test id)
  |> List.unique

let is_question_name str =
  str.[0] = '?'

let question_tids terms =
  extract_tids is_question_name terms

let is_capital_name str =
  match str.[0] with
    | 'A'..'Z' -> true
    | _ -> false

let capital_tids terms =
  extract_tids is_capital_name terms

let is_nominal_name str =
  Str.string_match (Str.regexp "^n[0-9]+$") str 0

let nominal_tids terms =
  extract_tids is_nominal_name terms

let all_tids terms =
  extract_tids (fun _ -> true) terms

let has_head test t =
  let rec aux t =
    match observe (hnorm t) with
      | Var v -> test v
      | App(h, _) -> aux h
      | _ -> false
  in
    aux t

let has_logic_head t =
  has_head (fun v -> v.tag = Logic) t

let has_eigen_head t =
  has_head (fun v -> v.tag = Eigen) t

(* Typing *)

let tyarrow tys ty =
  match ty with
    | Ty(tys', bty) -> Ty(tys @ tys', bty)

let tybase bty =
  Ty([], bty)

let oty = tybase "o"
let olistty = tybase "olist"

let rec tc (tyctx:tyctx) t =
  match observe (hnorm t) with
    | DB i -> snd (List.nth tyctx (i-1))
    | Var v -> v.ty
    | App(h,args) ->
        let arg_tys = List.map (tc tyctx) args in
        let Ty(tys, bty) = tc tyctx h in
        let n = List.length arg_tys in
          assert (List.take n tys = arg_tys) ;
          Ty(List.drop n tys, bty)
    | Lam(idtys,t) ->
        tyarrow (get_ctx_tys idtys) (tc (List.rev_app idtys tyctx) t)
    | _ -> assert false

let is_tyvar str =
  str.[0] = '?'

let tyvar str =
  tybase ("?" ^ str)

let fresh_tyvar =
  let count = ref 0 in
    fun () ->
      incr count ;
      tyvar (string_of_int !count)


let is_imp t = is_head_name "=>" t

let extract_imp t =
  match observe (hnorm t) with
    | App(t, [a; b]) -> (a, b)
    | _ -> failwith "Check is_imp before calling extract_imp"

let is_pi t = is_head_name "pi" t

let extract_pi t =
  match observe (hnorm t) with
    | App(t, [abs]) -> abs
    | _ -> failwith "Check is_pi before calling extract_pi"

let rec replace_pi_with_const term =
  let rec aux tyctx term =
    if is_pi term then
      let abs = extract_pi term in
      match observe (hnorm abs) with
      | Lam((id,ty)::_, _) ->
          let c = const id ty in
          aux ((id,ty)::tyctx) (app abs [c])
      | _ -> assert false
    else
      (tyctx, term)
  in
  aux [] term
