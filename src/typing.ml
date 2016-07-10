(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
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

open Term
open Metaterm
open Extensions
open Unifyty

(** Untyped terms *)

type uterm =
  | UCon of pos * string * ty
  | ULam of pos * string * ty * uterm
  | UApp of pos * uterm * uterm

let rec forget_term ?(cx=[]) t =
  match observe (hnorm t) with
  | Var v -> UCon (ghost, v.name, v.ty)
  | Lam ([], t) -> forget_term ~cx t
  | Lam ((x, xty) :: cx, t) ->
      ULam (ghost, x, xty, forget_term ~cx:((x, xty) :: cx) t)
  | App (f, ts) ->
      List.fold_left begin fun f t ->
        UApp (ghost, f, forget_term ~cx t)
      end (forget_term ~cx f) ts
  | DB n -> begin
      try
        let (x, xty) = List.nth cx (n - 1) in
        UCon (ghost, x, xty)
      with Failure _ -> bugf "forget_term called with too small a context"
    end
  | _ ->
      bugf "forget_term called on: %s" (term_to_string t)

let get_pos t =
  match t with
  | UCon(p, _, _) -> p
  | ULam(p, _, _, _) -> p
  | UApp(p, _, _) -> p

let change_pos p t =
  match t with
  | UCon(_, id, ty) -> UCon(p, id, ty)
  | ULam(_, id, ty, body) -> ULam(p, id, ty, body)
  | UApp(_, t1, t2) -> UApp(p, t1, t2)


let predefined id pos =
  UCon(pos, id, Term.fresh_tyvar ())

let binop id t1 t2 =
  let pos = (fst (get_pos t1), snd (get_pos t2)) in
  UApp(pos, UApp(pos, predefined id pos, t1), t2)


let uterm_head_name t =
  let rec aux = function
    | UCon(_, id, _) -> id
    | UApp(_, h, _) -> aux h
    | ULam _ -> assert false
  in
  aux t

(** Untyped metaterm *)

type umetaterm =
  | UTrue
  | UFalse
  | UEq of uterm * uterm
  | UAsyncObj of uterm * uterm * restriction
  | USyncObj of uterm * uterm * uterm * restriction
  | UArrow of umetaterm * umetaterm
  | UBinding of binder * (id * ty) list * umetaterm
  | UOr of umetaterm * umetaterm
  | UAnd of umetaterm * umetaterm
  | UPred of uterm * restriction

let apply_sub_tyctx s tyctx =
  List.map (fun (id, ty) -> (id, apply_sub_ty s ty)) tyctx

let ids_to_fresh_tyctx ids =
  List.map (fun id -> (id, fresh_tyvar ())) ids

let tyctx_to_ctx tyctx =
  List.map (fun (id, ty) -> (id, const id ty)) tyctx

let tyctx_to_nominal_ctx tyctx =
  List.map (fun (id, ty) -> (id, nominal_var id ty)) tyctx

(** Tables / Signatures *)

type ktable = (string * knd) list
type pty = Poly of string list * ty
type ctable = (string * pty) list
type sign = ktable * ctable

(** Kinds *)

let add_types (ktable, ctable) ids knd =
  List.iter begin fun id ->
    if is_capital_name id then
      failwithf "Types may not begin with a capital letter: %s" id
  end ids ;
  ((List.map (fun id -> (id, knd)) ids) @ ktable, ctable)

let lookup_type (ktable, _) id =
  List.assoc id ktable

(** Constants *)

let kind_check_poly sign ty =
  let rec aux = function
    | Ty(tys, AtmTy(cty,args)) ->
      List.iter aux args;
      let knd = 
        try lookup_type sign cty 
        with
        | Not_found -> failwithf "Unknown type constructor: %s" cty
      in
      let arity = karity knd in
      let nargs = List.length args in
      if nargs = arity then
        List.iter aux tys
      else
        failwithf "%s expects %i arguments but has %i" cty arity nargs
  in aux ty

let kind_check (ktable,ctable) (Poly(ids, ty)) = 
  let vknds = List.map (fun id -> (id, kind 0)) ids in
  kind_check_poly (vknds@ktable,ctable) ty

let check_const (ktable, ctable) (id, pty) =
  let rec targ_ty_not_var tyvars ty =
    match ty with
    | Ty(tys, AtmTy(cty, args)) ->
       if List.mem cty tyvars then
         let msg = 
           Printf.sprintf "Invalid type %s: target type cannot be a type variable" 
             (ty_to_string ty)
         in
         failwith msg
  in
  match pty with
  | Poly(ids, ty) -> targ_ty_not_var ids ty;
  begin try
    let pty' = List.assoc id ctable in
    if pty <> pty' then
      failwithf "Constant %s has inconsistent type declarations" id;
  with
  | Not_found -> ()
  end ;

  if is_capital_name id then
    failwithf "Constants may not begin with a capital letter: %s" id ;

  kind_check (ktable, ctable) pty

let add_poly_consts (ktable, ctable) idptys =
  List.iter (check_const (ktable, ctable)) idptys ;
  (ktable, idptys @ ctable)

let desugar_aty aty =
  match aty with
  | AtmTy("olist",[]) -> AtmTy("list",[oty])
  | _ -> aty

let rec desugar_ty ty =
  match ty with
  | Ty (tys, aty) ->
    let tys = List.map desugar_ty tys in
    let aty = desugar_aty aty in
    Ty (tys,aty)

let get_typaram ty = get_tycstr is_capital_name ty
let get_typarams tys = List.flatten_map get_typaram tys

let add_consts sign idtys =
  let typarams = idtys |> List.map snd |> List.map get_typaram in
  let idptys = List.map2 
    (fun (id, ty) params -> (id, Poly(params, ty))) idtys typarams in
  add_poly_consts sign idptys

let freshen_ty (Poly(ids, ty)) =
  let sub = ids_to_fresh_tyctx ids in
  apply_sub_ty sub ty

let lookup_const (_, ctable) id =
  try
    freshen_ty (List.assoc id ctable)
  with
  | Not_found -> failwithf "Unknown constant: %s" id

(** Pervasive signature *)

let k_fresh = "fresh_for"
let k_name = "is_name"
let k_member = "member"
let k_cons = "::"
let k_nil = "nil"

let pervasive_sign =
  let aty = tybase (atybase "A") in
  let alistty = tybase (atyapp (atybase "list") aty) in
  ([("o", Knd 0); ("list", Knd 1); ("prop", Knd 0)],
   [("pi",     Poly(["A"], tyarrow [tyarrow [aty] oty] oty)) ;
    ("=>",     Poly([],    tyarrow [oty; oty] oty)) ;
    ("&",      Poly([],    tyarrow [oty; oty] oty)) ;
    (k_cons,   Poly(["A"], tyarrow [aty; alistty] alistty)) ;
    (k_nil,    Poly(["A"], alistty)) ])

let sign_to_tys sign =
  List.filter_map
    (function (_, Poly([], ty)) -> Some ty | _ -> None)
    (snd sign)

let pervasive_sr =
  List.fold_left Subordination.update Subordination.empty
    (sign_to_tys pervasive_sign)

(** Typing for terms *)

let infer_type_and_constraints ~sign tyctx t =
  let eqns = ref [] in
  let add_constraint expected actual pos =
    eqns := (expected, actual, pos) :: !eqns
  in

  let rec aux tyctx t =
    match t with
    | UCon(p, id, ty) ->
        let ty' =
          begin try
            List.assoc id tyctx
          with
          | Not_found -> lookup_const sign id
          end
        in
        add_constraint ty ty' (p, CArg) ;
        ty
    | ULam(_, id, ty, t) ->
        tyarrow [ty] (aux ((id, ty) :: tyctx) t)
    | UApp(_, t1, t2) ->
        let ty1 = aux tyctx t1 in
        let ty2 = aux tyctx t2 in
        let (aty, rty) =
          match ty1 with
          | Ty([], _) ->
              let aty = fresh_tyvar () in
              let rty = fresh_tyvar () in
              add_constraint (tyarrow [aty] rty) ty1 (get_pos t1, CFun) ;
              (aty, rty)
          | Ty(aty::atys, bty) ->
              (aty, Ty(atys, bty))
        in
        add_constraint aty ty2 (get_pos t2, CArg) ;
        rty
  in

  let ty = aux tyctx t in
  (ty, List.rev !eqns)


let constraints_to_string eqns =
  let aux (ty1, ty2, _) =
    (ty_to_string ty1) ^ " = " ^ (ty_to_string ty2)
  in
  String.concat "\n" (List.map aux eqns)
  
let tid_ensure_fully_inferred ~sign (id, ty) =
  if contains_tyvar ty then
    failwithf "Type not fully determined for %s" id ;
  kind_check_poly sign ty

let term_ensure_fully_inferred ~sign t =
  let rec aux t =
    match observe (hnorm t) with
    | Var v -> tid_ensure_fully_inferred ~sign (v.name, v.ty)
    | DB i -> ()
    | App(h, args) -> aux h ; List.iter aux args
    | Lam(tys, body) -> 
       List.iter (tid_ensure_fully_inferred ~sign) tys; aux body
    | _ -> assert false
  in
  aux t

let metaterm_ensure_fully_inferred ~sign t =
  let rec aux t =
    match t with
    | True | False -> ()
    | And(a, b) | Or(a, b) | Arrow(a, b) -> aux a; aux b
    | Binding(_, tids, body) ->
        List.iter (tid_ensure_fully_inferred ~sign) tids ;
        aux body
    | Eq(a, b) ->
        term_ensure_fully_inferred ~sign a ;
        term_ensure_fully_inferred ~sign b
    | Obj(obj, _) ->
        Context.iter (term_ensure_fully_inferred ~sign) obj.context ;
        begin match obj.mode with
        | Async -> ()
        | Sync focus ->
            term_ensure_fully_inferred ~sign focus
        end ;
        term_ensure_fully_inferred ~sign obj.right
    | Pred(p, _) ->
        term_ensure_fully_inferred ~sign p
  in
  aux t

let uterms_extract_if test ts =
  let rec aux t =
    match t with
    | UCon(_, id, _) -> if test id then [id] else []
    | ULam(_, id, _, t) -> List.remove id (aux t)
    | UApp(_, t1, t2) -> (aux t1) @ (aux t2)
  in
  List.unique (List.flatten_map aux ts)

let uterm_nominals_to_tyctx t =
  ids_to_fresh_tyctx (uterms_extract_if is_nominal_name [t])

let uterm_to_term sub t =
  let rec aux t =
    match t with
    | UCon(_, id, ty) -> const id (apply_sub_ty sub ty)
    | ULam(_, id, ty, t) -> abstract id (apply_sub_ty sub ty) (aux t)
    | UApp(_, t1, t2) -> app (aux t1) [aux t2]
  in
  aux t

let uterm_to_string t =
  term_to_string (uterm_to_term [] t)

let term_ensure_subordination sr t =
  let rec aux tyctx t =
    match observe (hnorm t) with
    | Var v -> Subordination.ensure sr v.ty
    | DB i -> ()
    | App(h, ts) -> aux tyctx h ; List.iter (aux tyctx) ts
    | Lam(idtys, b) ->
        Subordination.ensure sr (tc tyctx t) ;
        aux (List.rev_app idtys tyctx) b
    | _ -> assert false
  in
  aux [] t

let iter_ty f ty =
  let rec aux = function
    | Ty(tys, bty) -> f bty; List.iter aux tys
  in
  aux ty

let check_spec_logic_type ty =
  iter_ty
    (fun (AtmTy(cty,args)) ->
       if cty = "prop" then
         failwith "Cannot mention type prop in the specification logic" ;
       if cty = "olist" then
         failwith "Cannot mention type olist in the specification logic")
    ty

let check_spec_logic_quantification_type ty =
  check_spec_logic_type ty ;
  iter_ty
    (fun (AtmTy(cty,args))  ->
       if cty = "o" then
         failwith "Cannot quantify over type o in the specification logic")
    ty

let check_pi_quantification ts =
  ignore
    (map_vars
       (fun v ->
          if v.name = "pi" then
            match v.ty with
            | Ty([Ty([tau], _)], _) ->
                check_spec_logic_quantification_type tau
            | _ -> assert false)
       ts)

let type_uterm ?(full_infer=true) ?expected_ty ~sr ~sign ~ctx t =
  let nominal_tyctx = uterm_nominals_to_tyctx t in
  let tyctx =
    (List.map (fun (id, t) -> (id, tc [] t)) ctx)
    @ nominal_tyctx
  in
  let (ty, eqns) = infer_type_and_constraints ~sign tyctx t in
  let eqns =
    match expected_ty with
    | None -> eqns
    | Some exp_ty -> (exp_ty, ty, (get_pos t, CArg)) :: eqns
  in
  let sub = unify_constraints eqns in
  let ctx = ctx @ (tyctx_to_nominal_ctx (apply_sub_tyctx sub nominal_tyctx)) in
  let result = replace_term_vars ctx (uterm_to_term sub t) in
  if full_infer then term_ensure_fully_inferred ~sign result ;
  term_ensure_subordination sr result ;
  result

let rec has_capital_head t =
  match t with
  | UCon(_, v, _) -> is_capital_name v
  | UApp(_, h, _) -> has_capital_head h
  | _ -> false


let replace_underscores head body =
  let names = uterms_extract_if is_capital_name (head::body) in
  let used = ref (List.map (fun x -> (x, ())) names) in
  let rec aux t =
    match t with
    | UCon(p, id, ty) when id = "_" ->
        let id' = fresh_name "X" !used in
        used := (id', ()) :: !used ;
        UCon(p, id', ty)
    | UCon _ -> t
    | ULam(p, id, ty, t) ->
        used := (id, ()) :: !used ;
        ULam(p, id, ty, aux t)
    | UApp(p, t1, t2) ->
        let t1' = aux t1 in
        let t2' = aux t2 in
        UApp(p, t1', t2')
  in
  match List.map aux (head::body) with
  | h::b -> (h, b)
  | [] -> assert false

let clause_map : term Itab.t ref = ref Itab.empty
let seen_name cname = Itab.mem cname !clause_map
let register_clause name clause =
  (* Printf.printf "Note: registered %S : %s\n%!" name *)
  (*   (Term.term_to_string clause) ; *)
  clause_map := Itab.add name clause !clause_map
let lookup_clause cname =
  if seen_name cname
  then Some (Itab.find cname !clause_map)
  else None

let check_clause t =
  let pres_tyvars (tids, head, body) =
    let htyvars = get_term_tyvars head in
    let btyvars = 
      List.fold_left begin fun vars t ->
        get_term_tyvars t @ vars
      end [] body 
    in
    List.for_all (fun v -> List.mem v htyvars) btyvars
  in
  let clauses = clausify t in
  if not (List.for_all pres_tyvars clauses) then
    failwithf 
      "The following program clause is not well-formed because there are type variables in its body that do not occur in its head:\n %s"
      (term_to_string t)

let type_uclause ~sr ~sign (cname, head, body) =
  if has_capital_head head then
    failwith "Clause has flexible (i.e., non-atomic) head" ;
  let head, body = replace_underscores head body in
  let cids = uterms_extract_if is_capital_name (head::body) in
  let get_imp_form head body =
    (let impfy imp f = (binop "=>" f imp) in
     List.fold_left impfy head (List.rev body))
  in
  let imp_form = get_imp_form head body in
  let get_pi_form ids body =
    (let pify id pi =
       let pos = get_pos pi in
       let abs = ULam (pos, id, Term.fresh_tyvar (), pi) in
       UApp (pos, predefined "pi" pos, abs)
     in
     List.fold_right pify ids body)
  in
  let pi_form = get_pi_form cids imp_form in
  let result = type_uterm ~full_infer:false ~sr ~sign ~ctx:[] pi_form in
  let _ = check_clause result in
  let _,cls = replace_pi_with_const result in
  let _ = check_pi_quantification [cls] in
  begin match cname with
  | None -> ()
  | Some cname ->
      if seen_name cname then
        failwithf "Clause named %S already seeen" cname ;
      register_clause cname result ;
  end ;
  result

(*
  let tyctx = ids_to_fresh_tyctx cids in
  let eqns =
    List.fold_left (fun acc p ->
                      let (pty, peqns) = infer_type_and_constraints ~sign tyctx p in
                        acc @ peqns @ [(oty, pty, (get_pos p, CArg))])
      [] (head::body)
  in
  let sub = unify_constraints eqns in
  let ctx = tyctx_to_ctx (apply_sub_tyctx sub tyctx) in
  let convert p = replace_term_vars ctx (uterm_to_term sub p) in
  let (rhead, rbody) = (convert head, List.map convert body) in
    List.iter term_ensure_fully_inferred (rhead::rbody) ;
    List.iter (term_ensure_subordination sr) (rhead::rbody) ;
    check_pi_quantification (rhead::rbody) ;
    (rhead, rbody)
*)


(** Typing for metaterms *)

let infer_constraints ~sign ~tyctx t =
  let rec aux tyctx t =
    match t with
    | UTrue | UFalse -> []
    | UEq(a, b) ->
        let (aty, aeqns) = infer_type_and_constraints ~sign tyctx a in
        let (bty, beqns) = infer_type_and_constraints ~sign tyctx b in
        aeqns @ beqns @ [(aty, bty, (get_pos b, CArg))]
    | UAsyncObj(l, g, _) ->
        let (lty, leqns) = infer_type_and_constraints ~sign tyctx l in
        let (gty, geqns) = infer_type_and_constraints ~sign tyctx g in
        leqns @ geqns @ [(olistty, lty, (get_pos l, CArg));
                         (oty, gty, (get_pos g, CArg))]
    | USyncObj(l, f, g, _) ->
        let (lty, leqns) = infer_type_and_constraints ~sign tyctx l in
        let (fty, feqns) = infer_type_and_constraints ~sign tyctx f in
        let (gty, geqns) = infer_type_and_constraints ~sign tyctx g in
        leqns @ feqns @ geqns @
        [(olistty, lty, (get_pos l, CArg));
         (oty, fty, (get_pos f, CArg));
         (oty, gty, (get_pos g, CArg))]
    | UArrow(a, b) | UOr(a, b) | UAnd(a, b) ->
        (aux tyctx a) @ (aux tyctx b)
    | UBinding(_, tids, body) ->
        aux (List.rev_app tids tyctx) body
    | UPred(p, _) ->
        let (pty, peqns) = infer_type_and_constraints ~sign tyctx p in
        peqns @ [(propty, pty, (get_pos p, CArg))]
  in
  aux tyctx t

let umetaterm_extract_if test t =
  let rec aux t =
    match t with
    | UTrue | UFalse -> []
    | UEq(a, b) ->
        uterms_extract_if test [a; b]
    | UPred(p, _) ->
        uterms_extract_if test [p]
    | UAsyncObj(l, g, _) ->
        uterms_extract_if test [l; g]
    | USyncObj(l, f, g, _) ->
        uterms_extract_if test [l;f;g]
    | UArrow(a, b) | UOr(a, b) | UAnd(a, b) ->
        (aux a) @ (aux b)
    | UBinding(_, tids, body) ->
        List.remove_all (fun id -> List.mem_assoc id tids) (aux body)
  in
  List.unique (aux t)

let umetaterm_nominals_to_tyctx t =
  ids_to_fresh_tyctx (umetaterm_extract_if is_nominal_name t)

let umetaterm_to_metaterm ?sign sub t =
  let rec aux t =
    match t with
    | UTrue -> True
    | UFalse -> False
    | UEq(a, b) -> Eq(uterm_to_term sub a, uterm_to_term sub b)
    | UAsyncObj(l, g, r) ->
        let context = Context.normalize [uterm_to_term sub l] in
        let right = uterm_to_term sub g in
        Obj({context ; right ; mode = Async}, r)
    | USyncObj(l, f, g, r) ->
        let context = Context.normalize [uterm_to_term sub l] in
        let right = uterm_to_term sub g in
        let mode = Sync (uterm_to_term sub f) in
        Obj({context ; right ; mode}, r)
    | UArrow(a, b) -> Arrow(aux a, aux b)
    | UBinding(binder, tids, body) ->
        (* let () = match sign with *)
        (*   | Some sign -> List.iter (fun (_, ty) -> kind_check_poly sign [] ty) tids *)
        (*   | None -> () *)
        (* in *)
        Binding(binder,
                List.map_snd (apply_sub_ty sub) tids,
                aux body)
    | UOr(a, b) -> Or(aux a, aux b)
    | UAnd(a, b) -> And(aux a, aux b)
    | UPred(p, r) -> Pred(uterm_to_term sub p, r)
  in
  aux t

let umetaterm_to_string ?sign t =
  metaterm_to_string (umetaterm_to_metaterm ?sign [] t)

let umetaterm_to_formatted_string ?sign t =
  metaterm_to_formatted_string (umetaterm_to_metaterm ?sign [] t)

let check_meta_logic_quantification_type ty =
  iter_ty
    (fun (AtmTy(cty,args)) ->
       if cty = "prop" then
         failwith "Cannot quantify over type prop")
    ty

let check_meta_quantification t =
  let rec aux t =
    match t with
    | True | False | Eq _ | Obj _ | Pred _ -> ()
    | And(a, b) | Or(a, b) | Arrow(a, b) -> aux a; aux b
    | Binding(_, tids, body) ->
        List.iter
          check_meta_logic_quantification_type
          (List.map snd tids) ;
        aux body
  in
  aux t

let make_async obj =
  match obj.mode with
  | Async -> obj
  | Sync focus ->
      { obj with
        mode = Async ;
        context = focus :: obj.context }

let metaterm_ensure_subordination sr t =
  let rec aux t =
    match t with
    | True | False -> ()
    | Eq(a, b) ->
        term_ensure_subordination sr a ;
        term_ensure_subordination sr b
    | Obj(obj, _) ->
        aux (async_to_member (make_async obj))
    | Arrow(a, b) | Or(a, b) | And(a, b) ->
        aux a ;
        aux b
    | Binding(_, tids, body) ->
        List.iter (Subordination.ensure sr) (List.map snd tids) ;
        aux body
    | Pred(p, _) ->
        term_ensure_subordination sr p
  in
  aux t

let type_umetaterm ~sr ~sign ?(ctx=[]) t =
  let nominal_tyctx = umetaterm_nominals_to_tyctx t in
  let tyctx =
    (List.map (fun (id, t) -> (id, tc [] t)) ctx)
    @ nominal_tyctx in
  let eqns = infer_constraints ~sign ~tyctx t in
  let sub = unify_constraints eqns in
  let ctx = ctx @ (tyctx_to_nominal_ctx (apply_sub_tyctx sub nominal_tyctx)) in
  let result = replace_metaterm_vars ctx (umetaterm_to_metaterm ~sign sub t) in
  metaterm_ensure_fully_inferred ~sign result ;
  metaterm_ensure_subordination sr result ;
  check_meta_quantification result ;
  result


let type_udef ~sr ~sign (head, body) =
  let cids = umetaterm_extract_if is_capital_name head in
  let tyctx = ids_to_fresh_tyctx cids in
  let eqns1 = infer_constraints ~sign ~tyctx head in
  let eqns2 = infer_constraints ~sign ~tyctx body in
  let sub = unify_constraints (eqns1 @ eqns2) in
  let ctx = tyctx_to_ctx (apply_sub_tyctx sub tyctx) in
  let (rhead, rbody) =
    (replace_metaterm_vars ctx (umetaterm_to_metaterm ~sign sub head),
     replace_metaterm_vars ctx (umetaterm_to_metaterm ~sign sub body))
  in
  metaterm_ensure_fully_inferred ~sign rhead ;
  metaterm_ensure_fully_inferred ~sign rbody ;
  metaterm_ensure_subordination sr rhead ;
  metaterm_ensure_subordination sr rbody ;
  check_meta_quantification rbody ;
  (rhead, rbody)

let type_udefs ~sr ~sign udefs =
  List.map (type_udef ~sr ~sign) udefs

(** Utilities *)

let rec has_capital_head t =
  match t with
  | UCon(_, id, _) -> is_capital_name id
  | ULam _ -> false
  | UApp(_, t, _) -> has_capital_head t

(** globals *)

let sign = State.rref pervasive_sign
let sr = State.rref pervasive_sr
