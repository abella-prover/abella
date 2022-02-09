(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006-2009 Nadathur, Linnell, Baelde, Ziegler, Gacek        *)
(* Copyright (C) 2013-2022 Inria (Institut National de Recherche            *)
(*                         en Informatique et en Automatique)               *)
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

let show_tag = false
let show_ty  = false
let show_ts  = false

open Extensions

type id = string

type tyvar = id
type tycons = id

type knd = Knd of int
type ty = Ty of ty list * aty
and aty =
  | Tygenvar of tyvar
  | Typtr of typtr
  | Tycons of tycons * ty list
and typtr = in_typtr ref
and in_typtr = TV of tyvar | TT of ty

(* Utilities for constructing and deconstructing terms *)

let rec observe_ty = function
  | Ty (args, aty) ->
     let args' = List.map observe_ty args in
     let targ =
       match aty with
       | Tycons (c, tys) ->
          let aargs = List.map observe_ty tys in
          Ty ([], Tycons (c, aargs))
       | Typtr {contents=TV _}
       | Tygenvar _ ->
          Ty ([], aty)
       | Typtr {contents=TT t} -> observe_ty t
     in
     let tyspine args t =
       match t with
       | Ty (args', targ) -> Ty (args@args', targ)
     in
     tyspine args' targ

let eq_ty ty1 ty2 = (observe_ty ty1 = observe_ty ty2)

let eq_tid (id1,ty1) (id2,ty2) =
  id1 = id2 && eq_ty ty1 ty2

let iter_ty f ty =
  let rec aux = function
    | Ty(tys, bty) ->
       List.iter aux tys;
       f bty;
       match bty with
       | Tycons (_c,args) -> List.iter aux args
       | Typtr {contents=TT _} -> assert false
       | _ -> ()
  in
  aux (observe_ty ty)

type tag = Eigen | Constant | Logic | Nominal

module Itab = Map.Make (String)
module Iset = struct
    include Set.Make (String)
    let of_list l =
      List.fold_left (fun s x -> add x s) empty l
  end

type var = {
  name : id ;
  tag  : tag ;
  ts   : int ;
  ty   : ty ;
}

let eq_var v1 v2 =
  v1.name = v2.name && v1.tag = v2.tag && v1.ts = v2.ts
  && eq_ty v1.ty v2.ty


type tyctx = (id * ty) list

type term =
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

let observe_var_ty v = {v with ty = observe_ty v.ty}

let rec observe = function
  | Ptr {contents=T d} -> observe d
  | Ptr {contents=V v} -> Var (observe_var_ty v)
  | t -> t


let rec deep_copy t =
  match t with
  | Ptr {contents = T t} -> deep_copy t
  | Lam (cx, t) -> Lam (cx, deep_copy t)
  | App (t, ts) -> App (deep_copy t, List.map deep_copy ts)
  | Susp (t, ol, nl, e) -> Susp (deep_copy t, ol, nl, deep_copy_env e)
  | Ptr _ | DB _ | Var _ -> t

and deep_copy_env e = List.map deep_copy_env_item e

and deep_copy_env_item item =
  match item with
  | Binding (t, n) -> Binding (deep_copy t, n)
  | Dum _ -> item

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
    | Var v1, Var v2 -> eq_var v1 v2
    | App(h1,l1), App(h2,l2) ->
        List.length l1 = List.length l2 &&
        List.for_all2 eq (h1::l1) (h2::l2)
    | Lam(idtys1,t1), Lam(idtys2,t2) ->
        List.for_all2 eq_ty (get_ctx_tys idtys1) (get_ctx_tys idtys2)
        && eq t1 t2
    | _ -> false

let eq_idterm (id1,t1) (id2,t2) =
  id1 = id2 && eq t1 t2

(* Binding a variable to a term. The *contents* of the cell representing the
 * variable is a reference which must be updated. Also the variable must
 * not be made a reference to itself. *)

(* bind_state for variables is a list of (var, old_value, new_value) *)
type bind_state_var = (ptr * in_ptr * term) list
let bind_state_var : bind_state_var ref = ref []

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
    bind_state_var := (dv, !dv, dt) :: !bind_state_var ;
    dv := T dt

(* Binding a type variable to a type, similar to binding of term variables *)

(* bind_state for type variables is a list of (tyvar, old_value, new_value) *)
type bind_state_ty = (typtr * in_typtr * ty) list
let bind_state_ty : bind_state_ty ref = ref []

let getref_ty = function
  | Typtr t -> t
  | _ -> assert false

let bind_ty v t =
  let dv = getref_ty v in
  let dt = observe_ty t in
    assert (match dt with Ty ([], Typtr r) -> dv != r | _ -> true) ;
    bind_state_ty := (dv, !dv, dt) :: !bind_state_ty ;
    dv := TT dt

(* Bind state consists of these of terms and types *)
type bind_state = bind_state_var * bind_state_ty

(* Retrieve or reset the bind state *)
let get_bind_state () = (!bind_state_var, !bind_state_ty)

let clear_bind_state () =
  List.iter (fun (v, ov, _nv) -> v := ov) !bind_state_var ;
  List.iter (fun (tv, tov, _tnv) -> tv := tov) !bind_state_ty ;
  bind_state_var := [] ;
  bind_state_ty := []

let set_bind_state (state_var, state_ty) =
  clear_bind_state () ;
  List.iter (fun (v, _ov, nv) -> bind (Ptr v) nv) (List.rev state_var) ;
  List.iter (fun (tv, _tov, tnv) -> bind_ty (Typtr tv) tnv) (List.rev state_ty)

(* make state undoable *)
let () = State.make () ~copy:get_bind_state ~assign:(fun () st -> set_bind_state st)

(* Scoped bind state is more efficient than regular bind state, but it
   must always be used in a lexically scoped fashion. The unwind_state
   wraps a function with a scoped get and set. *)

type scoped_bind_state = int * int

let get_bind_len () =
  (List.length (!bind_state_var), List.length (!bind_state_ty))
let get_scoped_bind_state () = get_bind_len ()

let set_scoped_bind_state_var state =
  while (List.length !bind_state_var) > state do
    match !bind_state_var with
      | (v, ov, _nv)::rest ->
          v := ov ;
          bind_state_var := rest ;
      | [] -> assert false
  done

let set_scoped_bind_state_ty state =
  while (List.length !bind_state_ty) > state do
    match !bind_state_ty with
      | (v, ov, _nv)::rest ->
          v := ov ;
          bind_state_ty := rest ;
      | [] -> assert false
  done

let set_scoped_bind_state (sv, st) =
  set_scoped_bind_state_var sv;
  set_scoped_bind_state_ty st

let unwind_state f x =
  let state = get_scoped_bind_state () in
  let result = f x in
  set_scoped_bind_state state ;
  result

(* Recursively raise dB indices and abstract over variables
 * selected by [test]. Indices unprotected by abstractions
 * are incremented. *)
let abstract test =
  let rec aux n t = match t with
    | DB i -> DB (if i < n then i else i + 1)
    | App(h,ts) -> App(aux n h, List.map (aux n) ts)
    | Lam(idtys,s) -> Lam (idtys, aux (n + List.length idtys) s)
    | Ptr {contents=T t} -> Ptr (ref (T (aux n t)))
    | Ptr {contents=V v} -> if test t v.name then DB n else t
    | Var _ -> assert false
    | Susp _ -> assert false
  in aux

(** Abstract [t] over constant or variable named [id]. *)
let abstract id ty t =
  lambda [(id,ty)] (abstract (fun _t id' -> id' = id) 1 t)

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
  let rec scan i =
    if i < 0 then 0 else
    match s.[i] with
    | '0' .. '9' -> scan (i - 1)
    | _ -> i + 1
  in
  let len = scan (String.length s - 1) in
  String.sub s 0 len

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
        | Lam (_idtys, t') -> fv acc t'
        | DB _ -> acc
        | Susp _ -> assert false
        | Ptr _ -> assert false
  in
    List.fold_left fv [] ts

let find_var_refs tag ts =
  List.unique ~cmp:eq (select_var_refs (fun v -> v.tag = tag) ts)

let find_vars tag ts =
  List.map term_to_var (find_var_refs tag ts)

let map_vars f ts =
  select_var_refs (fun _v -> true) ts
  |> List.rev
  |> List.unique ~cmp:eq
  |> List.map term_to_var
  |> List.map f

let get_used ts =
  select_var_refs (fun _v -> true) ts
  |> List.rev
  |> List.unique ~cmp:eq
  |> List.map (fun t -> ((term_to_var t).name, t))

(* Pretty printing *)

let tag2str = function
  | Constant -> "c"
  | Eigen -> "e"
  | Logic -> "l"
  | Nominal -> "n"

let abs_name = "x"

let arrow_op = Pretty.FMT " ->@ "
let space_op = Pretty.FMT " "

let rec pretty_ty (Ty (args, targ)) =
  let open Pretty in
  let args = List.map pretty_ty args in
  (* Pretty print format for atomic types *)
  let targ = pretty_aty targ in
  List.fold_right begin fun arg targ ->
    Opapp (1, Infix (RIGHT, arg, arrow_op, targ))
  end args targ

and pretty_aty aty =
  let open Pretty in
  match aty with
  | Tygenvar v
  | Typtr {contents=TV v} ->
     Atom (STR v)
  | Typtr {contents=TT _} -> assert false
  | Tycons (c,args) ->
     let cty = Atom (STR c) in
     let cargs = List.map pretty_ty args in
     List.fold_left begin fun aty arg ->
       Opapp (1, Infix (LEFT, aty, space_op, arg))
       end cty cargs

let format_ty fmt ty =
  Format.pp_open_box fmt 2 ; begin
    Pretty.print fmt (pretty_ty ty)
  end ; Format.pp_close_box fmt ()

let ty_to_string ty =
  let ty = observe_ty ty in
  let buf = Buffer.create 19 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_margin fmt max_int ;
  format_ty fmt ty ;
  Format.pp_print_flush fmt () ;
  Buffer.contents buf

let var_to_string v =
  let (bef, aft) = if show_tag || show_ts || show_ty then ("$(", ")") else ("", "") in
  bef ^ begin
    v.name
    ^ (if show_tag then "!" ^ tag2str v.tag else "")
    ^ (if show_ts then "/" ^ string_of_int v.ts else "")
    ^ (if show_ty then ":" ^ ty_to_string v.ty else "")
  end ^ aft

let rec knd_to_string = function
  | Knd 0 -> "Type"
  | Knd i -> "Type -> " ^ (knd_to_string (Knd (i-1)))

let atomic s = Pretty.(Atom (STR s))

let db_to_string cx0 i0 =
  let rec spin cx i =
    match cx, i with
    | [], _ -> abs_name ^ string_of_int (i0 - List.length cx0 + 1)
    | (x, _) :: _, 1 -> x
    | _ :: cx, _ -> spin cx (i - 1)
  in
  spin cx0 i0

let adjoin cx (x, ty) =
  let x' = fresh_name x cx in
  (x', ty) :: cx

let print_app f ts =
  let open Pretty in
  Bracket {
    left = STR "" ;
    right = STR "" ;
    trans = TRANSPARENT ;
    indent = 2 ;
    inner = List.fold_left begin fun f t ->
        Opapp (200, Infix (LEFT, f, FMT "@ ", t))
      end f ts }

class term_printer = object (self)
  method print (cx : tyctx) (t0 : term) =
    match observe (hnorm t0) with
    | Var v -> atomic (var_to_string v)
    | DB i -> atomic (db_to_string cx i)  (* ^ "$" ^ string_of_int i ^ "$") *)
    | Lam (vs, t) -> begin
        let tcx = map_vars (fun v -> (v.name, v.ty)) [t] in
        let rec spin cx vs =
          match vs with
          | [] -> self#print cx t
          | (x, ty) :: vs ->
              let x = fresh_name x tcx in
              let cx = adjoin cx (x, ty) in
              let x = fst (List.hd cx) in
              let tys = (if show_ty then ":" ^ ty_to_string ty else "") in
              Pretty.(Bracket { left = STR (x ^ tys ^ "\\") ;
                                right = STR "" ;
                                indent = 2 ;
                                inner = spin cx vs ;
                                trans = TRANSPARENT })
        in
        spin cx vs
      end
    | App (t, ts) -> begin
        match observe (hnorm t), ts with
        | Var {name="=>"; _}, [a; b] ->
            Pretty.(Opapp (100, Infix (RIGHT, self#print cx a,
                                     FMT " =>@ ", self#print cx b)))
        | Var {name="&"; _}, [a; b] ->
            Pretty.(Opapp (120, Infix (LEFT, self#print cx a,
                                     FMT " &@ ", self#print cx b)))
        | Var {name="::"; _}, [a; b] ->
            Pretty.(Opapp (130, Infix (RIGHT, self#print cx a,
                                       FMT " ::@ ", self#print cx b)))
        | Var {name=("pi"|"sigma" as q); _}, [a] -> begin
            match observe (hnorm a) with
            | Lam ([x, ty], t) ->
              let tys = (if show_ty then ":" ^ ty_to_string ty else "") in
                Pretty.(Opapp (50, Prefix (STR (q ^ " " ^ x ^ tys ^ "\\"),
                                           self#print (adjoin cx (x, ty)) t)))
            | a ->
                print_app Pretty.(Atom (STR "pi")) [self#print cx a]
          end
        | _ ->
            print_app (self#print cx t) (List.map (self#print cx) ts)
      end
    | _ -> assert false
end

let core_printer = new term_printer
let default_printer : term_printer ref = ref core_printer

let format_term ?(printer=(!default_printer)) ?(cx=[]) ff t =
  Format.pp_open_box ff 2 ; begin
    Pretty.print ff (printer#print cx t) ;
  end ; Format.pp_close_box ff ()

let term_to_string ?(printer=(!default_printer)) ?(cx=[]) t =
  let buf = Buffer.create 19 in
  let ff = Format.formatter_of_buffer buf in
  format_term ~printer ~cx ff t ;
  Format.pp_print_flush ff () ;
  Buffer.contents buf

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
    | Var {tag=Nominal; _} -> true
    | _ -> false

let term_head t =
  let rec aux t args =
    match hnorm t with
    | Ptr {contents = T t; _} -> aux t args
    | (Var _ | Ptr {contents = V _; _}) as t -> Some (t, args)
    | App (t, targs) -> aux t (targs @ args)
    | _ -> None
  in
  aux t []

let term_head_ty t =
  match term_head t with
  | None -> assert false
  | Some (h, _args) -> (term_to_var h).ty

let term_head_name t =
  match term_head t with
    | Some (t, _) -> term_to_name t
    | None -> assert false

let is_head_name name t =
  match term_head t with
    | Some (Ptr {contents=V v}, _) when v.name = name -> true
    | _ -> false

let extract_tids test terms =
  terms
  |> map_vars (fun v -> (v.name, v.ty))
  |> List.find_all (fun (id, _ty) -> test id)
  |> List.unique ~cmp:eq_tid

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

let rec all_numbers s pos len =
  pos >= len ||
  (s.[pos] >= '0' && s.[pos] <= '9' && all_numbers s (pos + 1) len)

let is_nominal_name str =
  String.length str > 1 &&
  str.[0] == 'n' &&
  all_numbers str 1 (String.length str)

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

(* Kinding *)
let kind i = Knd i
let kincr = function Knd i -> Knd (i+1)
let karity = function Knd i -> i

(* Typing *)
let atyvar str = Typtr (ref (TV (str)))
let atybase tyc = Tycons (tyc,[])
let atyapp aty ty =
  match aty with
  | Tycons (c,tys) -> Tycons (c, tys@[ty])
  | _ -> assert false

let tyarrow tys ty =
  match observe_ty ty with
    | Ty(tys', bty) -> Ty(tys @ tys', bty)

let tybase bty =
  Ty([], bty)

let aty_to_string aty =
  ty_to_string (tybase aty)

let oaty = (atybase "o")
let oty = tybase oaty
let olistaty = (atyapp (atybase "list") oty)
let olistty = tybase olistaty
let propaty = (atybase "prop")
let propty = tybase propaty


let rec tc (tyctx:tyctx) t =
  let ty =
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
  in observe_ty ty

let is_tyvar str =
  str.[0] = '?'

let tyvar str =
  Ty ([], atyvar ("?"^str))

let fresh_tyvar =
  let count = ref 0 in
    fun () ->
      incr count ;
      tyvar (string_of_int !count)


let is_imp t = is_head_name "=>" t

let extract_imp t =
  match observe (hnorm t) with
    | App(_t, [a; b]) -> (a, b)
    | _ -> bugf "Check is_imp before calling extract_imp"

let is_amp t = is_head_name "&" t
let extract_amp t =
  match observe (hnorm t) with
    | App(_t, [a; b]) -> (a, b)
    | _ -> bugf "Check is_amp before calling extract_amp"

let is_pi t = is_head_name "pi" t

let extract_pi t =
  match observe (hnorm t) with
    | App(_t, [abs]) -> abs
    | _ -> bugf "Check is_pi before calling extract_pi"


let term_map_on_tys f t =
  let rec taux t =
    match observe (hnorm t) with
    | Var v -> var v.tag v.name v.ts (f v.ty)
    | DB _ as t -> t
    | Lam (cx, t) ->
       lambda (List.map (fun (id,ty) -> (id, f ty)) cx) (taux t)
    | App (f, ts) -> app (taux f) (List.map taux ts)
    | Ptr _ | Susp _ -> assert false
  in
  taux t

let ty_tyvars ty =
  let tyvars = ref [] in
  let record aty =
    match aty with
    | Typtr {contents=TV v} ->
       tyvars := v::!tyvars
    | _ -> () in
  iter_ty record (observe_ty ty);
  !tyvars

let ty_contains_tyvar ty =
  List.length (ty_tyvars ty) > 0

let term_collect_tyvar_names t =
  let tyvars = ref [] in
  let _ = term_map_on_tys begin fun ty ->
            tyvars := (ty_tyvars ty)@(!tyvars); ty
            end t in
  List.unique (!tyvars)

let terms_contain_tyvar l =
  List.exists (fun t -> List.length (term_collect_tyvar_names t) <> 0) l

let ty_gentyvars ty =
  let tyvars = ref [] in
  let record aty =
    match aty with
    | Tygenvar v ->
       tyvars := v::!tyvars
    | _ -> () in
  iter_ty record ty;
  !tyvars

let ty_contains_gentyvar ty =
  List.length (ty_gentyvars ty) > 0

let term_collect_gentyvar_names t =
  let tyvars = ref [] in
  let _ = term_map_on_tys begin fun ty ->
            tyvars := (ty_gentyvars ty)@(!tyvars); ty
            end t in
  List.unique (!tyvars)

let terms_contain_gentyvar l =
  List.exists (fun t -> List.length (term_collect_gentyvar_names t) <> 0) l


(** Type substitutions *)

type tysub = (string * ty) list

let rec apply_bind_aty ~btyvar v ty aty =
  match aty with
  | Tygenvar v' ->
     if (not btyvar) && v' = v then ty
     else Ty ([], aty)
  | Typtr {contents=TV v'} ->
     if btyvar && v' = v then ty
     else Ty ([],aty)
  | Tycons (c,args) ->
     let args' = (List.map (apply_bind_ty ~btyvar v ty) args) in
     Ty ([], Tycons(c,args'))
  | Typtr {contents=TT _} -> assert false

and apply_bind_ty ~btyvar v ty t =
  match (observe_ty t) with
  | Ty(tys, aty) ->
     let tys' = (List.map (apply_bind_ty ~btyvar v ty) tys) in
     let aty' = apply_bind_aty ~btyvar v ty aty in
     tyarrow tys' aty'

let apply_sub_ty s ty =
  List.fold_left begin fun ty (v,vty) ->
    apply_bind_ty ~btyvar:false v vty ty
    end ty s

let apply_sub_ty_tyvar s ty =
  List.fold_left begin fun ty (v,vty) ->
    apply_bind_ty ~btyvar:true v vty ty
    end ty s


module Test = struct

  let p = const "p" (tyarrow [tybase (atybase "x")] oty)
  let q = const "q" (tyarrow [tybase (atybase "x")] oty)
  let mkpi x ty f =
    app (const "pi" (tyarrow [tyarrow [ty] oty] oty)) [lambda [x, ty] f]
  let mkimp f g =
    app (const "=>" (tyarrow [oty ; oty] oty)) [f ; g]
  let ity = tybase (atybase "i")
  let _t1 =
    mkpi "x" ity (mkimp (app p [db 1]) (app q [db 1]))
  let _t2 =
    mkimp (mkpi "x" ity (app p [db 1])) (app q [db 1])

end
