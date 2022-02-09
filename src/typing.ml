(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
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

open Term
open Metaterm
open Extensions
open Unifyty

(** Untyped terms *)

type pos = Lexing.position * Lexing.position

type uterm =
  | UCon of pos * string * ty
  | ULam of pos * string * ty * uterm
  | UApp of pos * uterm * uterm

let ghost : pos = (Lexing.dummy_pos, Lexing.dummy_pos)
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
    begin
      try
        let knd' = List.assoc id ktable in
        if knd <> knd' then
          failwithf "Type constructor %s has inconsistent kind declarations" id
      with
      | Not_found -> ()
    end ;

    if is_capital_name id then
      failwithf "Types may not begin with a capital letter: %s" id;
  end ids ;
  ((List.map (fun id -> (id, knd)) ids) @ ktable, ctable)

let lookup_type (ktable, _) id =
  List.assoc id ktable

(** Constants *)

let kind_check sign ty =
  let rec aux = function
    | Ty(tys, aty) ->
       List.iter aux tys;
       match aty with
       | Tygenvar _
       | Typtr {contents = TV _} -> ()
       | Tycons(cty,args) ->
          let knd =
            try lookup_type sign cty
            with
            | Not_found -> failwithf "Unknown type constructor: %s" cty
          in
          let arity = karity knd in
          let nargs = List.length args in
          if not (nargs = arity) then
            failwithf "%s expects %i arguments but has %i" cty arity nargs ;
          List.iter aux args
       | Typtr {contents = TT _} -> assert false
  in aux (observe_ty ty)

let kind_check_poly (ktable,ctable) (Poly(_ids, ty)) =
  kind_check (ktable,ctable) ty

let eq_pty pty1 pty2 =
  match pty1,pty2 with
  | Poly(ids1, ty1), Poly(ids2,ty2) ->
     List.length ids1 = List.length ids2 &&
     begin
       let tyvars = List.map (fun _ -> Term.fresh_tyvar ()) ids1 in
       let sub1 = List.map2 (fun id ty -> (id,ty)) ids1 tyvars in
       let sub2 = List.map2 (fun id ty -> (id,ty)) ids2 tyvars in
       let ty1' = apply_sub_ty sub1 ty1 in
       let ty2' = apply_sub_ty sub2 ty2 in
       eq_ty ty1' ty2'
     end

let check_const (ktable, ctable) (id, pty) =
  begin try
    let pty' = List.assoc id ctable in
    if not (eq_pty pty pty') then
      failwithf "Constant %s has inconsistent type declarations" id
  with
  | Not_found -> ()
  end ;

  if is_capital_name id then
    failwithf "Constants may not begin with a capital letter: %s" id ;

  kind_check_poly (ktable, ctable) pty

let add_poly_consts (ktable, ctable) idptys =
  List.iter (check_const (ktable, ctable)) idptys ;
  (ktable, idptys @ ctable)

let get_typaram ty =
  let params = ref [] in
  iter_ty begin fun aty ->
    match aty with
    | Tygenvar v ->
       if is_capital_name v then
         params := v::(!params)
    | _ -> ()
    end ty;
  !params

let get_typarams tys = List.flatten_map get_typaram tys

let add_consts sign idtys =
  let typarams = idtys |> List.map snd |> List.map get_typaram in
  let idptys = List.map2
                 (fun (id, ty) pas -> (id, Poly(pas, ty))) idtys typarams in
  add_poly_consts sign idptys

let freshen_ty (Poly(ids, ty)) =
  let sub = ids_to_fresh_tyctx ids in
  apply_sub_ty sub ty

let lookup_const (_, ctable) id =
  try
    freshen_ty (List.assoc id ctable)
  with
  | Not_found -> failwithf "Unknown constant: %s" id

(** Desugar types *)
let rec desugar_aty aty =
  match aty with
  | Tycons (v,tys) ->
     if v = "olist" && tys = [] then
       Tycons ("list",[oty])
     else
       let tys = List.map desugar_ty tys in
       Tycons (v,tys)
  | Typtr {contents=TT _t} ->
     assert false
  | _ -> aty

and desugar_ty ty =
  match (observe_ty ty) with
    | Ty (tys, aty) ->
       let tys = List.map desugar_ty tys in
       let aty = desugar_aty aty in
       Ty (tys,aty)

(** Pervasive signature *)

let k_member = "member"
let k_cons = "::"
let k_nil = "nil"

let pervasive_sign =
  let aty = tybase (Tygenvar "A") in
  let alistty = tybase (atyapp (atybase "list") aty) in
  ([("o", Knd 0); ("list", Knd 1); ("prop", Knd 0)],
   [("pi",     Poly(["A"], tyarrow [tyarrow [aty] oty] oty)) ;
    ("=>",     Poly([],    tyarrow [oty; oty] oty)) ;
    ("&",      Poly([],    tyarrow [oty; oty] oty)) ;
    (k_cons,   Poly(["A"], tyarrow [aty; alistty] alistty)) ;
    (k_nil,    Poly(["A"], alistty)) ])

let sign_to_tys sign =
  List.map
    (function (_, Poly(_ids, ty)) -> ty)
    (snd sign)

let pervasive_sr =
  List.fold_left Subordination.update Subordination.empty
    (sign_to_tys pervasive_sign)

(** Typing for terms *)

(* type expected = ty
 * type actual = ty
 * (\* A constraint contains the position of the 'actual' type *\)
 * type constraint_type = CFun | CArg
 * type constraint_info = pos * constraint_type
 * type constraints = (expected * actual * constraint_info) list
 * exception TypeInferenceFailure of constraint_info * expected * actual *)

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

(* let occurs v ty =
 *   let rec aux = function
 *     | Ty(tys, bty) when bty = v -> true
 *     | Ty(tys, _) -> List.exists aux tys
 *   in
 *   aux ty *)

let contains_tyvar ty =
  let rec aux = function
    | Ty (tys,aty) ->
       let cv =
         match aty with
         | Tygenvar _ -> false
         | Typtr {contents=TV _} -> true
         | Tycons (_c,args) ->
            List.exists aux args
         | Typtr {contents=TT _} -> assert false
       in
       cv || List.exists aux tys
  in aux (observe_ty ty)

let tid_ensure_fully_inferred ~sign (_id, ty) =
  if contains_tyvar ty then
    failwith "Types of variables are not fully determined" ;
  kind_check sign ty

let term_ensure_fully_inferred ~sign t =
  let rec aux t =
    match observe (hnorm t) with
    | Var v -> tid_ensure_fully_inferred ~sign (v.name, v.ty)
    | DB _i -> ()
    | App(h, args) -> aux h ; List.iter aux args
    | Lam(_tys, body) -> aux body
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

(* let apply_bind_constraints v ty eqns =
 *   List.map (fun (x,y) -> (apply_bind_ty v ty x, apply_bind_ty v ty y)) eqns
 *
 * let apply_bind_sub v ty sub =
 *   List.map (fun (x,y) -> (x, apply_bind_ty v ty y)) sub
 *
 * let unify_constraints eqns =
 *   let add_sub v vty s =
 *     (v, vty) :: (apply_bind_sub v vty s)
 *   in
 *
 *   (\* Unify a single constraint and call fail on failure *\)
 *   let rec aux s (ty1, ty2) fail =
 *     let ty1 = apply_sub_ty s ty1 in
 *     let ty2 = apply_sub_ty s ty2 in
 *     match ty1, ty2 with
 *     | _, _ when ty1 = ty2 -> s
 *     | Ty([], bty1), _ when is_tyvar bty1 ->
 *         if occurs bty1 ty2 then
 *           fail s
 *         else
 *           add_sub bty1 ty2 s
 *     | _, Ty([], bty2) when is_tyvar bty2 ->
 *         if occurs bty2 ty1 then
 *           fail s
 *         else
 *           add_sub bty2 ty1 s
 *     | Ty(ty1::tys1, bty1), Ty(ty2::tys2, bty2) ->
 *         let s = aux s (ty1, ty2) fail in
 *         aux s (Ty(tys1, bty1), Ty(tys2, bty2)) fail
 *     | ty1, ty2 -> fail s
 *   in
 *
 *   let unify_single_constraint s (ty1, ty2, p) =
 *     aux s (ty1, ty2)
 *       (fun s -> raise (TypeInferenceFailure(p, apply_sub_ty s ty1,
 *                                             apply_sub_ty s ty2)))
 *   in
 *
 *   List.fold_left unify_single_constraint [] eqns *)

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

let uterm_to_term t =
  let rec aux t =
    match t with
    | UCon(_, id, ty) -> const id ty
    | ULam(_, id, ty, t) -> abstract id ty (aux t)
    | UApp(_, t1, t2) -> app (aux t1) [aux t2]
  in
  aux t

let uterm_to_string t =
  term_to_string (uterm_to_term t)

let term_ensure_subordination sr t =
  let rec aux tyctx t =
    match observe (hnorm t) with
    | Var v -> Subordination.ensure sr v.ty
    | DB _i -> ()
    | App(h, ts) -> aux tyctx h ; List.iter (aux tyctx) ts
    | Lam(idtys, b) ->
        Subordination.ensure sr (tc tyctx t) ;
        aux (List.rev_app idtys tyctx) b
    | _ -> assert false
  in
  aux [] t

let check_spec_logic_type ty =
  iter_ty
    (fun bty ->
       if bty = propaty then
         failwith "Cannot mention type 'prop' in the specification logic" ;
       if bty = olistaty then
         failwith "Cannot mention type 'list o' in the specification logic")
    ty

let check_spec_logic_quantification_type ty =
  check_spec_logic_type ty ;
  iter_ty
    (fun bty  ->
       if bty = oaty then
         failwith "Cannot quantify over type o in the specification logic")
    ty

let check_pi_quantification ts =
  ignore
    (map_vars
       (fun v ->
          if v.name = "pi" then
            match observe_ty v.ty with
            | Ty([Ty([tau], _)], _) ->
                check_spec_logic_quantification_type tau
            | _ -> assert false)
       ts)

(* let get_tyvar_names ty =
 *   let rec aux = function
 *     | Ty (tys, aty) ->
 *        let ns = List.flatten_map aux tys in
 *        let ans =
 *          match aty with
 *          | Typtr {contents=TV v} -> [v]
 *          | Typtr {contents=TT _} -> assert false
 *          | Tygenvar _ -> []
 *          | Tycons (c,args) ->
 *             List.flatten_map aux tys
 *        in
 *        ns @ ans
 *   in List.unique (aux (observe_ty ty)) *)


let type_uterm ?partial_infer ?expected_ty ~sr ~sign ~ctx t =
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
  unify_constraints eqns;
  let ctx = ctx @ (tyctx_to_nominal_ctx nominal_tyctx) in
  let result = replace_term_vars ctx (uterm_to_term t) in
  (match partial_infer with
   | None -> term_ensure_fully_inferred ~sign result
   | Some _ -> ()) ;
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

let clause_map : (string list * term) Itab.t ref = ref Itab.empty
let seen_name cname = Itab.mem cname !clause_map
let register_clause name clause =
  (* Printf.printf "Note: registered %S : %s\n%!" name *)
  (*   (Term.term_to_string clause) ; *)
  clause_map := Itab.add name clause !clause_map
let lookup_clause cname =
  if seen_name cname
  then Some (Itab.find cname !clause_map)
  else None

let generalize_tyvars t =
  let tyvars = term_collect_tyvar_names t in
  let tysub = List.map (fun id -> (id, tybase (Tygenvar id))) tyvars in
  let t' = term_map_on_tys (apply_sub_ty_tyvar tysub) t in
  (tyvars, t')

let print_clause cl =
  let (vars, clause) = cl in
  let vstr = String.concat "," vars in
  let cstr = term_to_string clause in
  Printf.eprintf "Typed clause: [%s] %s\n" vstr cstr

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
  let result = type_uterm ~partial_infer:true ~sr ~sign ~ctx:[] pi_form in
  let result = generalize_tyvars result in
  (* print_clause result; *)
  let _ = check_pi_quantification [snd result] in
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

let umetaterm_to_metaterm ?sign:_ t =
  let rec aux t =
    match t with
    | UTrue -> True
    | UFalse -> False
    | UEq(a, b) -> Eq(uterm_to_term a, uterm_to_term b)
    | UAsyncObj(l, g, r) ->
        let context = Context.normalize [uterm_to_term l] in
        let right = uterm_to_term g in
        Obj({context ; right ; mode = Async}, r)
    | USyncObj(l, f, g, r) ->
        let context = Context.normalize [uterm_to_term l] in
        let right = uterm_to_term g in
        let mode = Sync (uterm_to_term f) in
        Obj({context ; right ; mode}, r)
    | UArrow(a, b) -> Arrow(aux a, aux b)
    | UBinding(binder, tids, body) ->
        (* let () = match sign with *)
        (*   | Some sign -> List.iter (fun (_, ty) -> kind_check_poly sign [] ty) tids *)
        (*   | None -> () *)
        (* in *)
        Binding(binder, tids, aux body)
    | UOr(a, b) -> Or(aux a, aux b)
    | UAnd(a, b) -> And(aux a, aux b)
    | UPred(p, r) -> Pred(uterm_to_term p, r)
  in
  aux t

let umetaterm_to_string ?sign t =
  metaterm_to_string (umetaterm_to_metaterm ?sign t)

let umetaterm_to_formatted_string ?sign t =
  metaterm_to_formatted_string (umetaterm_to_metaterm ?sign t)

let check_meta_logic_quantification_type ty =
  iter_ty
    (fun bty ->
       if bty = propaty then
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
  unify_constraints eqns;
  let ctx = ctx @ (tyctx_to_nominal_ctx nominal_tyctx) in
  let result = replace_metaterm_vars ctx (umetaterm_to_metaterm ~sign t) in
  metaterm_ensure_fully_inferred ~sign result ;
  metaterm_ensure_subordination sr result ;
  check_meta_quantification result ;
  result


let type_udef ~sr ~sign (head, body) =
  let cids = umetaterm_extract_if is_capital_name head in
  let tyctx = ids_to_fresh_tyctx cids in
  let eqns1 = infer_constraints ~sign ~tyctx head in
  let eqns2 = infer_constraints ~sign ~tyctx body in
  unify_constraints (eqns1 @ eqns2);
  let ctx = tyctx_to_ctx tyctx in
  let (rhead, rbody) =
    (replace_metaterm_vars ctx (umetaterm_to_metaterm ~sign head),
     replace_metaterm_vars ctx (umetaterm_to_metaterm ~sign body))
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

let sign : sign ref = State.rref pervasive_sign
let sr = State.rref pervasive_sr
