(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
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

open Term
open Extensions
open Format

type restriction =
  | Smaller of int
  | Equal of int
  | CoSmaller of int
  | CoEqual of int
  | Irrelevant

module Async =
struct
  type seq = { context : Context.t ;
                  term : term }
  let obj ctx t = { context = ctx ; term = t }
  let get obj = (obj.context, obj.term)
end

module Sync =
struct
  type seq = { context : Context.t ;
               focus   : term ;
               term    : term }
  let obj ctx f t = { context = ctx; focus = f; term = t }
  let get obj = (obj.context, obj.focus, obj.term)
end


type obj =
  | Async of Async.seq
  | Sync of Sync.seq

type binder =
  | Forall
  | Nabla
  | Exists

type metaterm =
  | True
  | False
  | Eq of term * term
  | Obj of obj * restriction
  | Arrow of metaterm * metaterm
  | Binding of binder * (id * ty) list * metaterm
  | Or of metaterm * metaterm
  | And of metaterm * metaterm
  | Pred of term * restriction

(* Constructions *)

let termobj t = Obj(Async(Async.obj Context.empty t), Irrelevant)
let arrow a b = Arrow(a, b)

let binding binder tids t =
  if tids = [] then
    t
  else
    match t with
      | Binding(binder', tids', t') when binder = binder' ->
          Binding(binder, tids @ tids', t')
      | _ -> Binding(binder, tids, t)

let rec conjoin mts =
  match mts with
  | [] -> True
  | [mt] -> mt
  | mt1 :: mt2 :: mts -> conjoin (And (mt1, mt2) :: mts)

let rec disjoin mts =
  match mts with
  | [] -> False
  | [mt] -> mt
  | mt1 :: mt2 :: mts -> disjoin (Or (mt1, mt2) :: mts)

let forall tids t = binding Forall tids t
let nabla tids t = binding Nabla tids t
let exists tids t = binding Exists tids t
let meta_or a b = Or(a, b)
let meta_and a b = And(a, b)
let pred p = Pred(p, Irrelevant)

let member_const = Term.const "member" (tyarrow [oty; olistty] propty)

let member e ctx =
  pred (app member_const [e; ctx])

let async_to_member obj =
  let (context, term) = Async.get obj in
  member term (Context.context_to_term context)

(* Support *)

let term_support ?(tag=Nominal) t = find_var_refs tag [t]
let term_list_support ?(tag=Nominal) l = find_var_refs tag l

let obj_support ?(tag=Nominal) = function
  | Async obj ->
      let ctx,term = Async.get obj in
      find_var_refs tag (term :: ctx)
  | Sync obj ->
      let ctx,focus,term = Sync.get obj in
      find_var_refs tag (term::focus::ctx)

let metaterm_support ?tag t =
  let rec aux t =
    match t with
      | True | False -> []
      | Eq(t1, t2) -> term_support ?tag t1 @ term_support ?tag t2
      | Obj(obj, _) -> obj_support ?tag obj
      | Arrow(t1, t2) -> aux t1 @ aux t2
      | Binding(_, _, t) -> aux t
      | Or(t1, t2) -> aux t1 @ aux t2
      | And(t1, t2) -> aux t1 @ aux t2
      | Pred(t, _) -> term_support ?tag t
  in
    List.unique (aux t)

(* Pretty printing *)

let show_types = State.rref false

let restriction_to_string r =
  match r with
  | Smaller i -> String.make i '*'
  | CoSmaller i -> String.make i '+'
  | Equal i -> String.make i '@'
  | CoEqual i -> String.make i '#'
  | Irrelevant -> ""

let bindings_to_string ts =
  String.concat " " (List.map fst ts)

let binder_to_string b =
  match b with
  | Forall -> "forall"
  | Nabla -> "nabla"
  | Exists -> "exists"

let pretty_context ~printer cx =
  let open Pretty in
  let open Format in
  let format ff =
    pp_open_box ff 0 ; begin
      Term.format_term ~printer ff (List.hd cx) ;
      List.iter begin fun t ->
        pp_print_string ff "," ;
        pp_print_space ff () ;
        Term.format_term ~printer ff t
      end (List.tl cx) ;
    end ; pp_close_box ff ()
  in
  Atom (FUN format)

let pretty_obj ~left ~right ~printer obj =
  let open Pretty in
  match obj with
  | Async {Async.context; Async.term} ->
      let concl = printer#print [] term in
      let inner = match context with
        | [] -> concl
        | _ -> Opapp (10, Infix (LEFT, pretty_context ~printer context,
                                 FMT " |-@ ", concl))
      in
      Bracket {
        left ; right ; indent = 3 ; trans = OPAQUE ; inner
      }
  | Sync {Sync.context; Sync.focus; Sync.term} ->
      let concl = printer#print [] term in
      let focus = Bracket {
          left = STR "[" ; right = STR "]" ; trans = OPAQUE ; indent = 3 ;
          inner = printer#print [] focus
        } in
      let hyps = match context with
        | [] -> focus
        | _ -> Opapp (10, Infix (LEFT, pretty_context ~printer context,
                                 FMT ",@ ", focus))
      in
      let inner = Opapp (10, Infix (LEFT, hyps, FMT " |-@ ", concl)) in
      Bracket {
        left ; right ; indent = 3 ; trans = OPAQUE ; inner
      }

let pretty_obj obj =
  let open Pretty in
  pretty_obj obj
    ~left:(STR "{") ~right:(STR "}")
    ~printer:Term.core_printer

let rec pretty_metaterm mt =
  let open Format in
  match mt with
  | True ->
      Pretty.(Atom (STR "true"))
  | False ->
      Pretty.(Atom (STR "false"))
  | Eq(a, b) ->
      Pretty.(Opapp (30, Infix (NON, core_printer#print [] a,
                                FMT " =@;<1 2>", core_printer#print [] b)))
  | Obj(obj, r) ->
      Pretty.(Opapp (50, Postfix (pretty_obj obj,
                                  STR (restriction_to_string r))))
  | Arrow(a, b) ->
      Pretty.(Opapp (20, Infix (RIGHT, pretty_metaterm a,
                                FMT " ->@;<1 2>", pretty_metaterm b)))
  | Or(a, b) ->
      Pretty.(Opapp (23, Infix (LEFT, pretty_metaterm a,
                                FMT " \\/@;<1 2>", pretty_metaterm b)))
  | And(a, b) ->
      Pretty.(Opapp (27, Infix (LEFT, pretty_metaterm a,
                                FMT " /\\@;<1 2>", pretty_metaterm b)))
  | Binding(q, tids, a) ->
      let binds = Pretty.(FUN begin
          fun ff ->
            pp_print_string ff (binder_to_string q) ;
            pp_print_string ff " " ;
            pp_open_box ff 0 ; begin
              pp_print_string ff (fst (List.hd tids)) ;
              List.iter begin fun tid ->
                pp_print_space ff () ;
                pp_print_string ff (fst tid)
              end (List.tl tids) ;
            end ; pp_close_box ff () ;
            pp_print_string ff ", " ;
        end) in
      let bod = pretty_metaterm a in
      Pretty.(Opapp (1, Prefix (binds, bod)))
  | Pred(p, Irrelevant) ->
      Term.core_printer#print [] p
  | Pred(p, r) ->
      Pretty.(Opapp (60, Postfix (Term.core_printer#print [] p,
                                  STR (" " ^ restriction_to_string r))))

let format_metaterm ff mt =
  let open Format in
  pp_open_vbox ff 0 ; begin
    if !show_types then begin
      let noms = metaterm_support mt |>
                 List.fast_sort (fun n1 n2 -> Stdlib.compare (term_head_name n1) (term_head_name n2))
      in
      if noms <> [] then begin
        pp_open_hovbox ff 1 ; begin
          pp_print_string ff "[" ;
          List.iter_sep ~sep:(pp_print_commaspace ff) begin fun nom ->
            pp_print_string ff (term_head_name nom) ;
            pp_print_string ff " : " ;
            pp_print_string ff (tc [] nom |> ty_to_string) ;
          end noms ;
          pp_print_string ff "]" ;
        end ; pp_close_box ff () ;
        pp_print_cut ff () ;
        pp_print_string ff "|> " ;
      end ;
    end ;
    pp_open_box ff 0 ; begin
      pretty_metaterm mt |> Pretty.print ff ;
    end ; pp_close_box ff () ;
  end ; pp_close_box ff ()

let metaterm_to_string t =
  let b = Buffer.create 50 in
  let fmt = formatter_of_buffer b in
    pp_set_margin fmt max_int ;
    format_metaterm fmt t ;
    pp_print_flush fmt () ;
    Buffer.contents b

let metaterm_to_formatted_string t =
  let b = Buffer.create 100 in
  let fmt = formatter_of_buffer b in
    format_metaterm fmt t ;
    pp_print_flush fmt () ;
    Buffer.contents b

(* Manipulations *)

let map_on_objs f t =
  let rec aux t =
    match t with
      | Obj(obj, r) -> Obj(f obj, r)
      | Arrow(a, b) -> Arrow(aux a, aux b)
      | Binding(binder, bindings, body) -> Binding(binder, bindings, aux body)
      | Or(a, b) -> Or(aux a, aux b)
      | And(a, b) -> And(aux a, aux b)
      | True | False | Eq _ | Pred _ -> t
  in
    aux t

let map_obj f = function
  | Async obj ->
      let (ctx, term) = Async.get obj in
      Async (Async.obj (Context.map f ctx) (f term))
  | Sync obj ->
      let (ctx, focus, term) = Sync.get obj in
      Sync (Sync.obj (Context.map f ctx) (f focus) (f term))

let map_terms f t =
  let rec aux t =
    match t with
    | True | False -> t
    | Eq(a, b) -> Eq(f a, f b)
    | Obj(obj, r) -> Obj(map_obj f obj, r)
    | Arrow(a, b) -> Arrow(aux a, aux b)
    | Binding(binder, bindings, body) ->
        Binding(binder, bindings, aux body)
    | Or(a, b) -> Or(aux a, aux b)
    | And(a, b) -> And(aux a, aux b)
    | Pred(p, r) -> Pred(f p, r)
  in
  aux t

let map_on_tys f mt =
  let rec aux mt =
    match mt with
    | True | False -> mt
    | Eq (a, b) -> Eq (taux a, taux b)
    | Obj (o, r) -> Obj (oaux o, r)
    | Arrow (f, g) -> Arrow (aux f, aux g)
    | Binding (q, bs, bod) ->
        Binding (q, List.map baux bs, aux bod)
    | Or (f, g) -> Or (aux f, aux g)
    | And (f, g) -> And (aux f, aux g)
    | Pred (p, r) -> Pred (taux p, r)
  and taux t =
    match observe (hnorm t) with
    | Var v -> var v.tag v.name v.ts (f v.ty)
    | DB _ as t -> t
    | Lam (cx, t) -> lambda (List.map baux cx) (taux t)
    | App (f, ts) -> app (taux f) (List.map taux ts)
    | Ptr _ | Susp _ -> assert false
  and oaux o =
    match o with
    | Async ao ->
        let (ctx, term) = Async.get ao in
        Async (Async.obj (Context.map taux ctx) (taux term))
    | Sync so ->
        let (ctx, foc, term) = Sync.get so in
        Sync (Sync.obj (Context.map taux ctx) (taux foc) (taux term))
  and baux (v, ty) = (v, f ty)
  in aux mt

type parity = EVEN | ODD
type posity = POS | NONPOS
let change_parity = function EVEN -> ODD | ODD -> EVEN
let relax_posity = function _ -> NONPOS

let iter_preds ?(parity=EVEN) ?(posity=POS) f term =
  let rec aux parity posity term =
    match term with
      | True | False | Eq _ | Obj _ -> ()
      | Arrow(a, b) ->
          aux (change_parity parity) (relax_posity posity) a ;
          aux parity posity b
      | Binding(_, _, body) ->
          aux parity posity body
      | Or(a, b) ->
          aux parity posity a ;
          aux parity posity b
      | And(a, b) ->
          aux parity posity a ;
          aux parity posity b
      | Pred(pred, _) ->
          f ~parity ~posity pred
  in
  aux parity posity term

let map_preds ?(parity=EVEN) ?(posity=POS) f term =
  let rec aux parity posity term =
    match term with
    | True | False | Eq _ | Obj _ -> []
    | Arrow(a, b) ->
        aux (change_parity parity) (relax_posity posity) a @
        aux parity posity b
    | Binding(_, _, body) ->
        aux parity posity body
    | Or(a, b) ->
        aux parity posity a @
        aux parity posity b
    | And(a, b) ->
        aux parity posity a @
        aux parity posity b
    | Pred(pred, _) -> [f ~parity ~posity pred]
  in
  aux parity posity term

let is_member = function
  | Pred (t,_) -> is_head_name "member" t
  | _ -> false

let extract_member = function
  | Pred (t,_) -> (
      match observe (hnorm t) with
      | App (t, [a;b]) -> (a,b)
      | _ -> bugf "Check is_member before calling extract_member")
  | _ -> bugf "Check is_member before calling extract_member"

let move_imp_to_context async_obj =
  let (ctx, term) = Async.get async_obj in
  let a, b = extract_imp term in
    Async.obj (Context.add a ctx) b


let is_async_obj t =
  match t with
  | Obj (Async _, _) -> true
  | _ -> false

let term_to_async_obj t =
  match t with
  | Obj (Async obj, _) -> obj
  | _ -> bugf "term_to_obj called on non-async-object"

let is_sync_obj t =
  match t with
    | Obj (Sync _,_) -> true
    | _ -> false


let term_to_sync_obj t =
  match t with
    | Obj(Sync obj, _) -> obj
    | _ -> bugf "term_to_obj called on non-sync-object"


let term_to_restriction t =
  match t with
    | Obj(_, r) -> r
    | Pred(_, r) -> r
    | _ -> Irrelevant

let set_restriction r t =
  match t with
    | Obj(obj, _) -> Obj(obj, r)
    | Pred(p, _) -> Pred(p, r)
    | _ -> bugf "Attempting to set restriction to non-object"

let reduce_inductive_restriction r =
  match r with
    | Equal i -> Smaller i
    | _ -> r

let reduce_coinductive_restriction r =
  match r with
    | CoEqual i -> CoSmaller i
    | _ -> r

let add_to_context elt async_obj =
  let (ctx, term) = Async.get async_obj in
  Async.obj (Context.add elt ctx) term

let sig_to_string (name, arity) = name ^ "/" ^ (string_of_int arity)

(* Variable Renaming *)

let fresh_alist ~used ~tag tids =
  let used = ref used in
    List.map (fun (x, ty) ->
                (* Timestamps should always be 0 for user visible variables *)
                let (fresh, curr_used) = fresh_wrt ~ts:0 tag x ty !used in
                  used := curr_used ;
                  (x, fresh))
      tids

let raise_type ~sr support ty =
  let rsupport =
    List.filter (fun x -> Subordination.query sr (tc [] x) ty) support
  in
  let rtys = List.map (tc []) rsupport in
    (tyarrow rtys ty, rsupport)

let fresh_raised_alist ~used ~sr ~tag ~support tids =
  let ids, tys = List.split tids in
  let rtys, rsupports = List.split (List.map (raise_type ~sr support) tys) in
  let alist = fresh_alist ~used ~tag (List.combine ids rtys) in
    (List.map2 (fun (id, t) support -> (id, app t support)) alist rsupports,
     List.map snd alist)

let replace_term_vars ?tag alist t =
  let rec aux t =
    match observe (hnorm t) with
      | Var v when List.mem_assoc v.name alist &&
          (tag = None || tag = Some v.tag)
          ->
          List.assoc v.name alist
      | Var _
      | DB _ -> t
      | Lam(i, t) -> lambda i (aux t)
      | App(t, ts) -> app (aux t) (List.map aux ts)
      | Susp _ -> assert false
      | Ptr _ -> assert false
  in
    aux t

let rec replace_metaterm_vars alist t =
  let term_aux alist = replace_term_vars alist in
  let rec aux alist t =
    match t with
      | True | False -> t
      | Eq(a, b) -> Eq(term_aux alist a, term_aux alist b)
      | Obj(obj, r) -> Obj(map_obj (term_aux alist) obj, r)
      | Arrow(a, b) -> Arrow(aux alist a, aux alist b)
      | Binding(binder, bindings, body) ->
          let alist = List.remove_assocs (List.map fst bindings) alist in
          let used = get_used (List.map snd alist) in
          let bindings_alist = fresh_alist ~tag:Constant ~used bindings in
          let bindings' =
            List.map (fun (_, t) -> let v = term_to_var t in (v.name, v.ty))
              bindings_alist
          in
            Binding(binder,
                    bindings',
                    aux (alist @ bindings_alist) body)
      | Or(a, b) -> Or(aux alist a, aux alist b)
      | And(a, b) -> And(aux alist a, aux alist b)
      | Pred(p, r) -> Pred(term_aux alist p, r)
  in
    aux alist t

let rec collect_terms t =
  match t with
    | True | False -> []
    | Eq(a, b) -> [a; b]
    | Obj(Async obj, _) ->
        let (ctx,term) = Async.get obj in
        (Context.context_to_list ctx) @ [term]
    | Obj(Sync obj, _) ->
        let (ctx,focus,term) = Sync.get obj in
        (Context.context_to_list ctx) @ [focus;term]
    | Arrow(a, b) -> (collect_terms a) @ (collect_terms b)
    | Binding(_, _, body) -> collect_terms body
    | Or(a, b) -> (collect_terms a) @ (collect_terms b)
    | And(a, b) -> (collect_terms a) @ (collect_terms b)
    | Pred(p, _) -> [p]

let map_term_list f t = List.map f (collect_terms t)

let get_metaterm_used t =
  t |> collect_terms
    |> find_var_refs Eigen
    |> List.map term_to_pair

let get_metaterm_used_nominals t =
  t |> metaterm_support
    |> List.map term_to_pair

let fresh_nominals_by_list tys used_names =
  let p = prefix Nominal in
  let result = ref [] in
  let get_name () =
    let n = ref 1 in
      while List.mem (p ^ (string_of_int !n)) (!result @ used_names) do
        incr n
      done ;
      p ^ (string_of_int !n)
  in
    for i = 1 to List.length tys do
      result := !result @ [get_name()] ;
    done ;
    List.map2 nominal_var !result tys

let fresh_nominals tys t =
  let used_vars = find_vars Nominal (collect_terms t) in
  let used_names = List.map (fun v -> v.name) used_vars in
    fresh_nominals_by_list tys used_names

let fresh_nominal ty t =
  match fresh_nominals [ty] t with
    | [n] -> n
    | _ -> assert false

let replace_pi_with_nominal async_obj =
  let ctx,term = Async.get async_obj in
  let abs = extract_pi term in
    match tc [] abs with
      | Ty(ty::_, _) ->
          let nominal = fresh_nominal ty (Obj(Async async_obj, Irrelevant)) in
          Async.obj ctx (app abs [nominal])
      | _ -> assert false

let rec normalize_obj obj =
  let rec aux async_obj =
    let ctx,term = Async.get async_obj in
    if is_imp term then
      aux (move_imp_to_context async_obj)
    else if is_pi term then
      aux (replace_pi_with_nominal async_obj)
    else
      Async.obj (Context.normalize ctx) term
  in
  let norm_ctx sync_obj =
    let ctx,focus,term = Sync.get sync_obj in
    Sync.obj (Context.normalize ctx) focus term
  in
  match obj with
  | Async obj -> Async (aux obj)
  | Sync obj -> Sync (norm_ctx obj)

let normalize_binders =
  let aux_term rens t = replace_term_vars ~tag:Constant rens t in
  let rec aux rens used form = match form with
    | True | False -> form
    | Eq (a, b)    -> Eq (aux_term rens a, aux_term rens b)
    | Obj (obj, r) -> Obj (map_obj (aux_term rens) obj, r)
    | Arrow (a, b) -> Arrow (aux rens used a, aux rens used b)
    | Or (a, b)    -> Or (aux rens used a, aux rens used b)
    | And (a, b)   -> And (aux rens used a, aux rens used b)
    | Pred (p, r)  -> Pred (aux_term rens p, r)
    | Binding (binder, bvars, body) ->
        let (rens, used, rev_bvars) = List.fold_left begin
            fun (rens, used, bvars) (v, ty) ->
              if List.mem_assoc v used then begin
                let (fv, used) = fresh_wrt ~ts:0 Constant v ty used in
                let rens = (v, fv) :: rens in
                (* Printf.fprintf stderr "Freshened %s to %s [used = %s]\n%!" *)
                (*   v (term_to_name fv) *)
                (*   (String.concat "," (List.map fst used)) ; *)
                let bvars = (term_to_name fv, ty) :: bvars in
                (rens, used, bvars)
              end else begin
                let used = term_to_pair (var Constant v 0 ty) :: used in
                let bvars = (v, ty) :: bvars in
                (rens, used, bvars)
              end
          end (rens, used, []) bvars
        in
        let bvars = List.rev rev_bvars in
        (* Printf.fprintf stderr "Descended under: %s; used = %s\n%!" *)
        (*   (String.concat "," (List.map fst bvars)) *)
        (*   (String.concat "," (List.map fst used)) ; *)
        binding binder bvars (aux rens used body)
  in
  fun form ->
    let used = get_metaterm_used form @ get_metaterm_used_nominals form in
    aux [] used form

let replace_term_typed_nominals alist t =
  let rec aux t =
    match observe (hnorm t) with
      | Var v when v.tag = Nominal && List.mem_assoc (v.name, v.ty) alist ->
          List.assoc (v.name, v.ty) alist
      | Var _
      | DB _ -> t
      | Lam(i, t) -> lambda i (aux t)
      | App(t, ts) -> app (aux t) (List.map aux ts)
      | Susp _ -> assert false
      | Ptr _ -> assert false
  in
    aux t

let rec replace_metaterm_typed_nominals alist t =
  let term_aux = replace_term_typed_nominals alist in
  let rec aux t =
    match t with
      | True | False -> t
      | Eq(a, b) -> Eq(term_aux a, term_aux b)
      | Obj(obj, r) -> Obj(map_obj term_aux obj, r)
      | Arrow(a, b) -> Arrow(aux a, aux b)
      | Binding(binder, bindings, body) ->
          Binding(binder, bindings, aux body)
      | Or(a, b) -> Or(aux a, aux b)
      | And(a, b) -> And(aux a, aux b)
      | Pred(p, r) -> Pred(term_aux p, r)
  in
    aux t

let normalize_nominals t =
  let used_names = ref [] in
  let shadowed =
    List.filter_map
      (fun t ->
         let v = term_to_var t in
           if List.mem v.name !used_names then
             Some (v.name, v.ty)
           else begin
             used_names := v.name :: !used_names;
             None
           end)
      (metaterm_support t)
  in
  let nominals = fresh_nominals_by_list (List.map snd shadowed) !used_names in
  let nominal_alist = List.combine shadowed nominals in
    replace_metaterm_typed_nominals nominal_alist t

let normalize term =
  term
  |> map_on_objs normalize_obj
  |> normalize_nominals
  |> normalize_binders

let make_nabla_alist tids body =
  let (id_names, id_tys) = List.split tids in
  let nominals = fresh_nominals id_tys body in
    List.combine id_names nominals

(* Error reporting *)

let invalid_metaterm_arg t =
  invalid_arg (metaterm_to_string t)

(* Unification *)

open Unify

let rec meta_right_unify t1 t2 =
  match t1, t2 with
    | True, True -> ()
    | False, False -> ()
    | Eq(l1, r1), Eq(l2, r2) ->
        right_unify l1 l2 ;
        right_unify r1 r2
    | Obj(Async o1, _), Obj(Async o2, _) when
        (let ctx1,_ = Async.get o1 in
        let ctx2,_ = Async.get o2 in
        Context.equiv ctx1 ctx2) ->
          let _,term1 = Async.get o1 in
          let _,term2 = Async.get o2 in
          right_unify term1 term2
    | Pred(t1, _), Pred(t2, _) ->
        right_unify t1 t2
    | And(l1, r1), And(l2, r2)
    | Or(l1, r1), Or(l2, r2)
    | Arrow(l1, r1), Arrow(l2, r2) ->
        meta_right_unify l1 l2 ;
        meta_right_unify r1 r2
    | Binding(b1, tids1, t1), Binding(b2, tids2, t2)
        when b1 = b2 && List.map snd tids1 = List.map snd tids2 ->
        (* Replace bound variables with constants with "infinite"
           timestamp. This prevents illegal variable capture.
           We use max_int-1 since max_int is for nominal constants. *)
        let new_bindings =
          List.map (fun (_, ty) -> fresh ~tag:Constant (max_int-1) ty) tids1
        in
        let alist1 = List.combine (List.map fst tids1) new_bindings in
        let alist2 = List.combine (List.map fst tids2) new_bindings in
          meta_right_unify
            (replace_metaterm_vars alist1 t1)
            (replace_metaterm_vars alist2 t2)
    | _, _ -> raise (UnifyFailure Generic)

let try_meta_right_unify t1 t2 =
  try_with_state ~fail:false
    (fun () ->
       meta_right_unify t1 t2 ;
       true)

(* Try to unify t1 and t2 under permutations of nominal constants.
   For each successful unification, call sc.
   t1 may contain logic variables, t2 is ground                    *)
let all_meta_right_permute_unify ~sc t1 t2 =
  let support_t1 = metaterm_support t1 in
  let support_t2 = metaterm_support t2 in
    if List.length support_t1 < List.length support_t2 then
      (* Ground term cannot have more nominals than logic term *)
      ()
    else
      let support_t2_names = List.map term_to_name support_t2 in
        support_t1
        |> List.permute (List.length support_t2)
        |> List.iter
            (unwind_state
               (fun perm_support_t1 ->
                  let alist = List.combine support_t2_names perm_support_t1 in
                    if try_meta_right_unify t1 (replace_metaterm_vars alist t2) then sc ()))

(* Check for derivability between objects under permutations. Need
   goal.term to unify with hyp.term and also hyp.context subcontext
   of goal.context. Can assume hyp is ground *)
let derivable_sync goal hyp =
  let gctx,gfocus,gterm = Sync.get goal in
  let hctx,hfocus,hterm = Sync.get hyp in
  let support_g = obj_support (Sync goal) in
  let support_h = obj_support (Sync hyp) in
    if List.length support_g < List.length support_h then
      false
    else
      let support_h_names = List.map term_to_name support_h in
        support_g |> List.permute (List.length support_h)
          |> List.exists
              (fun perm_support_g ->
                 let alist = List.combine support_h_names perm_support_g in
                   try_right_unify gterm
                     (replace_term_vars alist hterm) &&
                 (Context.subcontext
                    (Context.map (replace_term_vars alist) (hfocus::hctx))
                    (gfocus::gctx)))

let derivable_async goal hyp =
  let gctx,gterm = Async.get goal in
  let hctx,hterm = Async.get hyp in
  let support_g = obj_support (Async goal) in
  let support_h = obj_support (Async hyp) in
    if List.length support_g < List.length support_h then
      false
    else
      let support_h_names = List.map term_to_name support_h in
        support_g |> List.permute (List.length support_h)
          |> List.exists
              (fun perm_support_g ->
                 let alist = List.combine support_h_names perm_support_g in
                   try_right_unify gterm
                     (replace_term_vars alist hterm) &&
                     (Context.subcontext
                        (Context.map (replace_term_vars alist) hctx)
                        gctx))

let metaterm_extract_tids aux_term t =
  let aux_obj = function
    | Async obj ->
        let ctx,term = Async.get obj in
        aux_term ctx @ aux_term [term]
    | Sync obj ->
        let ctx,focus,term = Sync.get obj in
        aux_term ctx @ aux_term [focus;term]
  in
  let rec aux = function
    | True | False -> []
    | Eq(a, b) -> aux_term [a; b]
    | Obj(obj, r) -> aux_obj obj
    | Arrow(a, b) -> aux a @ aux b
    | Binding(binder, bindings, body) ->
        List.remove_all (fun (id, ty) -> List.mem_assoc id bindings) (aux body)
    | Or(a, b) -> aux a @ aux b
    | And(a, b) -> aux a @ aux b
    | Pred(p, r) -> aux_term [p]
  in
    List.unique (aux t)

let metaterm_capital_tids t =
  metaterm_extract_tids capital_tids t

let metaterm_nominal_tids t =
  metaterm_extract_tids nominal_tids t

let def_head_name head =
  let rec aux t =
    match t with
      | Pred(p, _) -> term_head_name p
      | Binding(_, _, t) -> aux t
      | _ -> assert false
  in
    aux head

let def_head_args head =
  let rec aux = function
    | Pred (p, _) -> begin
        match term_head p with
        | Some (_, args) -> args
        | None -> bugf "Cannot find arguments!"
      end
    | Binding (_, _, t) -> aux t
    | _ -> assert false
  in
  aux head

(* Make (head,body) tuples from clauses.
   The conversion from a term clause to a
   (head, body) pair without prefixe binders
   is required for unification. It is also
   used in some test cases.
*)
let clausify term =
  let (tyctx, term') = replace_pi_with_const term in
  let rec move_imps obj =
    let ctx,term = Async.get obj in
    if is_imp term then
      move_imps (move_imp_to_context obj)
    else
      Async.obj (Context.normalize ctx) term in
  let body,head = Async.get (move_imps (Async.obj Context.empty term'))
  in
  (tyctx,head,body)
