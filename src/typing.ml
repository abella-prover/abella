open Term
open Metaterm
open Extensions

module H = Hashtbl


(** Untyped terms *)

type pos = Lexing.position * Lexing.position

type uterm =
  | UCon of pos * string * ty
  | ULam of pos * string * ty * uterm
  | UApp of pos * uterm * uterm

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

(** Untyped metaterm *)

type umetaterm =
  | UTrue
  | UFalse
  | UEq of uterm * uterm
  | UObj of uterm * uterm * restriction
  | UArrow of umetaterm * umetaterm
  | UBinding of binder * (id * ty) list * umetaterm
  | UOr of umetaterm * umetaterm
  | UAnd of umetaterm * umetaterm
  | UPred of uterm * restriction


(** Type substitutions *)

type tysub = (string * ty) list

let rec apply_bind_ty v ty = function
  | Ty(tys, bty) ->
      tyarrow
        (List.map (apply_bind_ty v ty) tys)
        (if v = bty then ty else Ty([], bty))

let apply_sub_ty s ty =
  List.fold_left (fun ty (v,vty) -> apply_bind_ty v vty ty) ty s

let apply_sub_tyctx s tyctx =
  List.map (fun (id, ty) -> (id, apply_sub_ty s ty)) tyctx

let ids_to_fresh_tyctx ids =
  List.map (fun id -> (id, fresh_tyvar ())) ids

let tyctx_to_ctx tyctx =
  List.map (fun (id, ty) -> (id, const id ty)) tyctx

let tyctx_to_nominal_ctx tyctx =
  List.map (fun (id, ty) -> (id, nominal_var id ty)) tyctx


(** Kind table *)

type ktable = (string, unit) H.t
let ktable : ktable = H.create 10

let check_type id =
  if H.mem ktable id then
    failwith (id ^ " has already been declared as a type")

let add_types ids =
  List.iter check_type ids ;
  List.iter (fun id -> H.add ktable id ()) ids

let lookup_type id =
  H.mem ktable id

let () =
  add_types ["o"; "olist"; "prop"]


(** Constants *)

type pty = Poly of string list * ty
type ctable = (string, pty) H.t
let ctable : ctable = H.create 10

let rec kind_check = function
  | Ty(tys, bty) ->
      if lookup_type bty then
        List.iter kind_check tys
      else
        failwith ("Unknown type: " ^ bty)

let check_const (id, ty) =
  if H.mem ctable id then
    failwith (id ^ " has already been declared as a constant")
  else if is_capital_name id then
    failwith ("Constants may not begin with a capital letter: " ^ id)
  else
    kind_check ty

let add_consts idtys =
  match List.find_duplicate (List.map fst idtys) with
    | Some id -> failwith (id ^ " is defined mutiple times")
    | None ->
        List.iter check_const idtys ;
        List.iter (fun (id, ty) -> H.add ctable id (Poly([], ty))) idtys

let () =
  H.add ctable "pi" (Poly(["A"], (tyarrow [tyarrow [tybase "A"] oty] oty))) ;
  add_consts [("=>", tyarrow [oty; oty] oty) ;
              ("member", tyarrow [oty; olistty] propty) ;
              ("::", tyarrow [oty; olistty] olistty) ;
              ("nil", olistty)]

let freshen_ty (Poly(ids, ty)) =
  let sub = ids_to_fresh_tyctx ids in
    apply_sub_ty sub ty

let lookup_const id =
  try
    freshen_ty (H.find ctable id)
  with
    | Not_found -> failwith ("Unknown constant: " ^ id)


(** Typing for terms *)

type expected = ty
type actual = ty
(* A constraint contains the position of the 'actual' type *)
type constraint_type = CFun | CArg
type constraint_info = pos * constraint_type
type constraints = (expected * actual * constraint_info) list
exception TypeInferenceFailure of constraint_info * expected * actual

let infer_type_and_constraints tyctx t =
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
              | Not_found -> lookup_const id
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

let occurs v ty =
  let rec aux = function
    | Ty(tys, bty) when bty = v -> true
    | Ty(tys, _) -> List.exists aux tys
  in
    aux ty

let rec contains_tyvar = function
  | Ty(tys, bty) ->
      is_tyvar bty || List.exists contains_tyvar tys

let tid_ensure_fully_inferred (id, ty) =
  if contains_tyvar ty then
    failwith ("Type not fully determined for " ^ id)

let term_ensure_fully_inferred t =
  let rec aux t =
    match observe (hnorm t) with
      | Var v -> tid_ensure_fully_inferred (v.name, v.ty)
      | DB i -> ()
      | App(h, args) -> aux h ; List.iter aux args
      | Lam(tys, body) -> aux body
      | _ -> assert false
  in
    aux t

let metaterm_ensure_fully_inferred t =
  let rec aux t =
    match t with
      | True | False -> ()
      | And(a, b) | Or(a, b) | Arrow(a, b) -> aux a; aux b
      | Binding(_, tids, body) ->
          List.iter tid_ensure_fully_inferred tids ;
          aux body
      | Eq(a, b) ->
          term_ensure_fully_inferred a ;
          term_ensure_fully_inferred b
      | Obj(obj, _) ->
          Context.iter term_ensure_fully_inferred obj.context ;
          term_ensure_fully_inferred obj.term
      | Pred(p, _) ->
          term_ensure_fully_inferred p
  in
    aux t

let apply_bind_constraints v ty eqns =
  List.map (fun (x,y) -> (apply_bind_ty v ty x, apply_bind_ty v ty y)) eqns

let apply_bind_sub v ty sub =
  List.map (fun (x,y) -> (x, apply_bind_ty v ty y)) sub

let unify_constraints eqns =
  let add_sub v vty s =
      (v, vty) :: (apply_bind_sub v vty s)
  in

  (* Unify a single constraint and call fail on failure *)
  let rec aux s (ty1, ty2) fail =
    let ty1 = apply_sub_ty s ty1 in
    let ty2 = apply_sub_ty s ty2 in
      match ty1, ty2 with
        | _, _ when ty1 = ty2 -> s
        | Ty([], bty1), _ when is_tyvar bty1 ->
            if occurs bty1 ty2 then
              fail s
            else
              add_sub bty1 ty2 s
        | _, Ty([], bty2) when is_tyvar bty2 ->
            if occurs bty2 ty1 then
              fail s
            else
              add_sub bty2 ty1 s
        | Ty(ty1::tys1, bty1), Ty(ty2::tys2, bty2) ->
            let s = aux s (ty1, ty2) fail in
              aux s (Ty(tys1, bty1), Ty(tys2, bty2)) fail
        | ty1, ty2 -> fail s
  in

  let unify_single_constraint s (ty1, ty2, p) =
    aux s (ty1, ty2)
      (fun s -> raise (TypeInferenceFailure(p, apply_sub_ty s ty1,
                                            apply_sub_ty s ty2)))
  in

    List.fold_left unify_single_constraint [] eqns

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


let type_uterm ~ctx t expected_ty =
  let nominal_tyctx = uterm_nominals_to_tyctx t in
  let tyctx =
    (List.map (fun (id, t) -> (id, tc [] t)) ctx)
      @ nominal_tyctx
  in
  let (ty, eqns) = infer_type_and_constraints tyctx t in
  let eqns = (expected_ty, ty, (get_pos t, CArg)) :: eqns in
  let sub = unify_constraints eqns in
  let ctx = ctx @ (tyctx_to_nominal_ctx (apply_sub_tyctx sub nominal_tyctx)) in
  let result = replace_term_vars ctx (uterm_to_term sub t) in
    term_ensure_fully_inferred result ;
    result

let rec has_capital_head t =
  match t with
    | UCon(_, v, _) -> is_capital_name v
    | UApp(_, h, _) -> has_capital_head h
    | _ -> false

let iter_ty f ty =
  let rec aux = function
    | Ty(tys, bty) -> f bty; List.iter aux tys
  in
    aux ty

let check_spec_logic_type ty =
  iter_ty
    (fun bty ->
       if bty = "prop" then
         failwith "Cannot mention type prop in the specification logic" ;
       if bty = "olist" then
         failwith "Cannot mention type olist in the specification logic")
    ty

let check_spec_logic_quantification_type ty =
  check_spec_logic_type ty ;
  iter_ty
    (fun bty  ->
        if bty = "o" then
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

let type_uclause (head, body) =
  if has_capital_head head then
    failwith "Clause has flexible head" ;
  let cids = uterms_extract_if is_capital_name (head::body) in
  let tyctx = ids_to_fresh_tyctx cids in
  let eqns =
    List.fold_left (fun acc p ->
                      let (pty, peqns) = infer_type_and_constraints tyctx p in
                        acc @ peqns @ [(oty, pty, (get_pos p, CArg))])
      [] (head::body)
  in
  let sub = unify_constraints eqns in
  let ctx = tyctx_to_ctx (apply_sub_tyctx sub tyctx) in
  let convert p = replace_term_vars ctx (uterm_to_term sub p) in
  let (rhead, rbody) = (convert head, List.map convert body) in
    List.iter term_ensure_fully_inferred (rhead::rbody) ;
    check_pi_quantification (rhead::rbody) ;
    (rhead, rbody)


(** Typing for metaterms *)

let infer_constraints ~tyctx t =
  let rec aux tyctx t =
    match t with
      | UTrue | UFalse -> []
      | UEq(a, b) ->
          let (aty, aeqns) = infer_type_and_constraints tyctx a in
          let (bty, beqns) = infer_type_and_constraints tyctx b in
            aeqns @ beqns @ [(aty, bty, (get_pos b, CArg))]
      | UObj(l, g, _) ->
          let (lty, leqns) = infer_type_and_constraints tyctx l in
          let (gty, geqns) = infer_type_and_constraints tyctx g in
            leqns @ geqns @ [(olistty, lty, (get_pos l, CArg));
                             (oty, gty, (get_pos g, CArg))]
      | UArrow(a, b) | UOr(a, b) | UAnd(a, b) ->
          (aux tyctx a) @ (aux tyctx b)
      | UBinding(_, tids, body) ->
          aux ((List.rev tids) @ tyctx) body
      | UPred(p, _) ->
          let (pty, peqns) = infer_type_and_constraints tyctx p in
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
      | UObj(l, g, _) ->
          uterms_extract_if test [l; g]
      | UArrow(a, b) | UOr(a, b) | UAnd(a, b) ->
          (aux a) @ (aux b)
      | UBinding(_, tids, body) ->
          List.remove_all (fun id -> List.mem_assoc id tids) (aux body)
  in
    List.unique (aux t)

let umetaterm_nominals_to_tyctx t =
  ids_to_fresh_tyctx (umetaterm_extract_if is_nominal_name t)

let umetaterm_to_metaterm sub t =
  let rec aux t =
    match t with
      | UTrue -> True
      | UFalse -> False
      | UEq(a, b) -> Eq(uterm_to_term sub a, uterm_to_term sub b)
      | UObj(l, g, r) ->
          Obj({context = Context.normalize [uterm_to_term sub l] ;
               term = uterm_to_term sub g}, r)
      | UArrow(a, b) -> Arrow(aux a, aux b)
      | UBinding(binder, tids, body) ->
          Binding(binder,
                  List.map_snd (apply_sub_ty sub) tids,
                  aux body)
      | UOr(a, b) -> Or(aux a, aux b)
      | UAnd(a, b) -> And(aux a, aux b)
      | UPred(p, r) -> Pred(uterm_to_term sub p, r)
  in
    aux t

let umetaterm_to_string t =
  metaterm_to_string (umetaterm_to_metaterm [] t)

let umetaterm_to_formatted_string t =
  metaterm_to_formatted_string (umetaterm_to_metaterm [] t)

let check_meta_logic_quantification_type ty =
  iter_ty
    (fun bty ->
       if bty = "prop" then
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

let type_umetaterm ?(ctx=[]) t =
  let nominal_tyctx = umetaterm_nominals_to_tyctx t in
  let tyctx =
    (List.map (fun (id, t) -> (id, tc [] t)) ctx)
      @ nominal_tyctx
  in
  let eqns = infer_constraints ~tyctx t in
  let sub = unify_constraints eqns in
  let ctx = ctx @ (tyctx_to_nominal_ctx (apply_sub_tyctx sub nominal_tyctx))
  in
  let result = replace_metaterm_vars ctx (umetaterm_to_metaterm sub t) in
    metaterm_ensure_fully_inferred result ;
    check_meta_quantification result ;
    result


let type_udef (head, body) =
  let cids = umetaterm_extract_if is_capital_name head in
  let tyctx = ids_to_fresh_tyctx cids in
  let eqns1 = infer_constraints ~tyctx head in
  let eqns2 = infer_constraints ~tyctx body in
  let sub = unify_constraints (eqns1 @ eqns2) in
  let ctx = tyctx_to_ctx (apply_sub_tyctx sub tyctx) in
  let (rhead, rbody) =
    (replace_metaterm_vars ctx (umetaterm_to_metaterm sub head),
     replace_metaterm_vars ctx (umetaterm_to_metaterm sub body))
  in
    metaterm_ensure_fully_inferred rhead ;
    metaterm_ensure_fully_inferred rbody ;
    check_meta_quantification rbody ;
    (rhead, rbody)

let type_udefs udefs =
  List.map type_udef udefs

(** Utilities *)

let rec has_capital_head t =
  match t with
    | UCon(_, id, _) -> is_capital_name id
    | ULam _ -> false
    | UApp(_, t, _) -> has_capital_head t
