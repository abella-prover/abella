(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006-2009 Nadathur, Linnell, Baelde, Ziegler, Gacek        *)
(* Copyright (C) 2013-2016 Inria (Institut National de Recherche            *)
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

type knd = Knd of int
type aty = AtmTy of string * ty list
and  ty = Ty of ty list * aty

type tag = Eigen | Constant | Logic | Nominal
type id = string

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

let rec observe = function
  | Ptr {contents=T d} -> observe d
  | Ptr {contents=V v} -> Var v
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

let rec norm t =
  match observe (hnorm t) with
  | (Var _ | DB _) as t -> t
  | App (f, ts) -> App (norm f, List.map norm ts)
  | Lam (cx, t) -> Lam (cx, norm t)
  | _ -> assert false

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

(* make state undoable *)
let () = State.make () ~copy:get_bind_state ~assign:(fun () st -> set_bind_state st)

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
       
(* apply f to types in a term *)
let iter_term_tys f t =
  let rec aux t =
    match observe (hnorm t) with
    | Var v -> f v.ty
    | DB i -> ()
    | App(h, args) -> aux h ; List.iter aux args
    | Lam(tys, body) -> 
       List.iter (fun (id,ty) -> f ty) tys ; aux body
    | _ -> assert false
  in
  aux t

let map_on_term_tys f t =
  let rec taux t = match observe (hnorm t) with
  | Var v -> var v.tag v.name v.ts (f v.ty)
  | DB _ as t -> t
  | Lam (cx, t) -> lambda (List.map baux cx) (taux t)
  | App (f, ts) -> app (taux f) (List.map taux ts)
  | Ptr _ | Susp _ -> assert false
  and baux (v, ty) = (v, f ty) 
  in
  taux t


(* Pretty printing *)

exception Found of int

type assoc = Left | Right | Both | No

(* List of infix operators sorted by priority, low to high. *)
let infix : (string * assoc) list =
  [("=>", Right); ("&", Left); ("::", Right)]

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

let arrow_op = Pretty.FMT " ->@ "
let space_op = Pretty.FMT " "
let rec pretty_ty (Ty (args, AtmTy(cty,cargs))) =
  let open Pretty in
  let args = List.map pretty_ty args in
  let cargs = List.map pretty_ty cargs in
  let cty = Atom (STR cty) in
  let targ = 
    List.fold_left begin fun aty arg ->
      Opapp (1, Infix (LEFT, aty, space_op, arg))
    end cty cargs
  in
  List.fold_right begin fun arg targ ->
    Opapp (1, Infix (RIGHT, arg, arrow_op, targ))
  end args targ
let format_ty fmt ty =
  Format.pp_open_box fmt 2 ; begin
    Pretty.print fmt (pretty_ty ty)
  end ; Format.pp_close_box fmt ()
let ty_to_string ty =
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
    
let infix_ops : (id * (Pretty.atom * Pretty.assoc * Pretty.prec)) list =
  let open Pretty in
  [ "=>" , (FMT " =>@ " , RIGHT , 1) ;
    "&"  , (FMT " &@ "  , LEFT  , 2) ;
    "::" , (FMT " ::@ " , LEFT  , 3) ]
let is_infix op = List.exists (fun (o, _) -> o = op) infix_ops
let prefix_ops = [ "pi" ; "sigma" ]
let is_prefix op = List.mem op prefix_ops

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
              Pretty.(Bracket { left = STR (x ^ "\\") ;
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
                Pretty.(Bracket { left = STR (q ^ " " ^ x ^ "\\") ;
                                  right = STR "" ;
                                  indent = 2 ;
                                  inner = self#print (adjoin cx (x, ty)) t ;
                                  trans = TRANSPARENT })
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
    | Var {tag=Nominal; name=name; ts=ts; ty=ty} -> true
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
let atybase tyc = AtmTy(tyc,[]) 
let atyapp aty ty =
  match aty with
  | AtmTy(tyc,tys) -> AtmTy(tyc,tys@[ty])
 
let tyarrow tys ty =
  match ty with
    | Ty(tys', bty) -> Ty(tys @ tys', bty)

let tybase aty =
  Ty([], aty)

let oty = tybase (atybase "o")
let olistty = tybase (atyapp (atybase "list") oty)
let propty = tybase (atybase "prop")

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

let is_gen_tyvar str =
  str.[0] = '#'

let name_of_gen_tyvar str = 
  assert (is_gen_tyvar str);
  let len = String.length str in
  String.sub str 1 (len-1)

let tyvar str =
  tybase (atybase ("?" ^ str))

let fresh_tyvar =
  let count = ref 0 in
    fun () ->
      incr count ;
      tyvar (string_of_int !count)

let tag_gen_tyvar str = "#" ^ str

let rec mark_gen_tyvar gen_tyvars ty =
  let aux = mark_gen_tyvar gen_tyvars in
  match ty with
  | Ty (tys, AtmTy(cty, args)) ->
     let tys' = List.map aux tys in
     let args' = List.map aux args in
     let cty' = if List.mem cty gen_tyvars 
       then tag_gen_tyvar cty else cty in
     Ty (tys', AtmTy(cty', args'))

let rec contains_tyvar = function
  | Ty(tys, AtmTy(cty, args)) ->
      is_tyvar cty || 
      List.exists contains_tyvar tys ||
      List.exists contains_tyvar args

let rec contains_gen_tyvar ty =
  match ty with
  | Ty (tys, (AtmTy (cty, args))) ->
    is_gen_tyvar cty ||
    List.exists contains_gen_tyvar tys ||
    List.exists contains_gen_tyvar args

let term_contains_tyvar t =
  let has_tyvar = ref false in
  let f ty = 
    has_tyvar := !has_tyvar || contains_tyvar ty
  in
  iter_term_tys f t;
  !has_tyvar

let term_contains_gen_tyvar t =
  let has_gen_tyvar = ref false in
  let f ty = 
    has_gen_tyvar := !has_gen_tyvar || 
      contains_gen_tyvar ty
  in
  iter_term_tys f t;
  !has_gen_tyvar
  
let is_poly_term t =
  term_contains_tyvar t || term_contains_gen_tyvar t


(** Type substitutions *)
type tysub = (string * ty) list

let rec apply_bind_ty v ty = function
  | Ty(tys, (AtmTy(cty,args))) ->
    let tys = (List.map (apply_bind_ty v ty) tys) in
    let targ = 
      if v = cty then
        (assert (args = []); ty)
      else
        tybase (AtmTy(cty, (List.map (apply_bind_ty v ty) args)))
    in tyarrow tys targ

let apply_sub_ty s ty =
  List.fold_left (fun ty (v,vty) -> apply_bind_ty v vty ty) ty s

let apply_bind_sub v ty sub =
  List.map (fun (x,y) -> (x, apply_bind_ty v ty y)) sub

let is_ground_tysub sub =
  not (List.exists (fun (id,ty) -> contains_tyvar ty) sub)

let inst_poly_term sub t =
  map_on_term_tys (apply_sub_ty sub) t
    
let term_fully_instantiated t =
  let insted = ref true in
  let f ty =
    insted := !insted && not (contains_tyvar ty)
  in
  iter_term_tys f t;
  !insted

(* Manipulation of clauses *)
let is_imp t = is_head_name "=>" t

let extract_imp t =
  match observe (hnorm t) with
    | App(t, [a; b]) -> (a, b)
    | _ -> bugf "Check is_imp before calling extract_imp"

let is_amp t = is_head_name "&" t
let extract_amp t =
  match observe (hnorm t) with
    | App(t, [a; b]) -> (a, b)
    | _ -> bugf "Check is_amp before calling extract_amp"

let is_pi t = is_head_name "pi" t

let extract_pi t =
  match observe (hnorm t) with
    | App(t, [abs]) -> abs
    | _ -> bugf "Check is_pi before calling extract_pi"

let rec replace_pi_with_const term =
  let rec aux tyctx term =
    if is_pi term then
      let abs = extract_pi term in
      let (c, ty) = match observe (hnorm abs) with
        | Lam ((id, ty) :: _, _) -> (const id ty, ty)
        | _ -> begin
            match tc [] abs with
            | Ty (ty :: tys, targy) ->
                let x = fresh ~tag:Constant 0 ty in
                (x, ty)
            | _ ->
                bugf "Cannot determine the type of a pi: %s" (term_to_string term)
          end
      in
      aux ((term_to_name c, ty)::tyctx) (app abs [c])
    else
      (tyctx, term)
  in
  aux [] term
