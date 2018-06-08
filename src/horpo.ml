(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015-2018  Inria (Institut National de Recherche
 *                          en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Higher-order recursive path ordering

   Based on: J.-P. Jouannand and A. Rubio, "The Higher-Order Recursive
   Path Ordering", LICS 1999 *)


open Term
open Abella_types

open Extensions

let geq ?(gt=(>)) s t =
  Term.eq s t || gt s t

let rec splits left x right =
  match right with
  | [] -> [x, List.rev left]
  | r :: right1 -> (x, List.rev_append left right) :: splits (x :: left) r right1
let splits l = match l with
  | [] -> []
  | x :: l -> splits [] x l

let rec multiset_extension ?(gt=(>)) set1 set2 =
  splits set1 |>
  List.exists begin fun (s, set1) ->
    let set2 = List.filter (fun t -> not (gt s t)) set2 in
    List.length (List.intersect ~cmp:Term.eq set1 set2) =
    List.length set1
  end

let rec lex_extension ?(gt=(>)) ss tt =
  match ss, tt with
  | (s :: ss), (t :: tt) ->
      gt s t || (Term.eq s t && lex_extension ~gt ss tt)
  | [], [] -> false
  | [], _  -> true
  | _, []  -> false

let rec remove_common_prefix ss tt =
  match ss, tt with
  | [], _ | _, [] -> ([], ss, tt)
  | (s :: ss), (_ :: tt) ->
      let (cx, ss, tt) = remove_common_prefix ss tt in
      (s :: cx, ss, tt)

let is_var t =
  match observe (hnorm t) with
  | Var _ -> true
  | _ -> false

let unapply t =
  match term_head t with
  | Some (h, sp) -> (h, sp)
  | None -> (t, [])

let muls : (string, unit) Hashtbl.t = State.table ()
let register_mul s = Hashtbl.replace muls s ()
let is_mul s = Hashtbl.mem muls s

let rpo_basic ~gt s0 ss tt =
  List.for_all begin fun t ->
    gt s0 t ||
    List.exists (fun s -> geq ~gt s t) ss
  end tt

let partial_flats h ts =
  let splits = ref [] in
  let emit s t = splits := (s, t) :: !splits in
  let rec spin pre post =
    match post with
    | [] | [_] -> ()
    | t :: post ->
        let pre = app pre [t] in
        emit pre post ; spin pre post
  in
  spin h ts ;
  List.rev_append !splits [h, ts]

let rec horpo ?(cx=[]) s0 t0 =
  let sty = tc cx s0 in
  let tty = tc cx t0 in
  sty = tty &&
  match observe (hnorm s0), observe (hnorm t0) with
  | DB m, DB n   -> m > n
  | Lam (scx, s), Lam (tcx, t) ->
      let (ccx, scx, tcx) = remove_common_prefix scx tcx in
      let s = lambda scx s in
      let t = lambda tcx t in
      horpo ~cx:(List.rev_append ccx cx) s t
  | s0, t0 ->
      let open Delim in
      reset begin fun here ->
        let (sh, ss) = unapply s0 in
        let (th, tt) = unapply t0 in
        if is_var sh then begin
          if List.exists (fun s -> geq ~gt:(horpo ~cx) s t0) ss
          then shift here true ;
          if is_var th then begin
            let sh = term_to_name sh in
            let th = term_to_name th in
            if sh > th &&
               rpo_basic ~gt:(horpo ~cx) s0 ss tt
            then shift here true ;
            if sh = th then begin
              if is_mul sh &&
                 multiset_extension ~gt:(horpo ~cx) ss tt
              then shift here true ;
              if not (is_mul sh) &&
                 lex_extension ~gt:(horpo ~cx) ss tt &&
                 rpo_basic ~gt:(horpo ~cx) s0 ss tt
              then shift here true ;
            end ;
          end
        end else begin
          partial_flats th tt |>
          List.iter begin fun (th, tt) ->
            let tt = th :: tt in
            if rpo_basic ~gt:(horpo ~cx) s0 ss tt then shift here true ;
          end ;
          begin match List.rev ss, List.rev tt with
          | (s :: ss), (t :: tt) ->
              let ss = List.rev ss in
              let tt = List.rev tt in
              let sh = app sh ss in
              let th = app th tt in
              if multiset_extension ~gt:(horpo ~cx) [sh ; s] [th ; t]
              then shift here true
          | _ -> ()
          end
        end ;
        false
      end

let metaterm_inject =
  let k_true      = const "#<true>"    propty                            in
  let k_false     = const "#<false>"   propty                            in
  let k_and       = const "#<and>"    (tyarrow [propty ; propty] propty) in
  let k_or        = const "#<or>"     (tyarrow [propty ; propty] propty) in
  let k_arrow     = const "#<arrow>"  (tyarrow [propty ; propty] propty) in
  let k_forall ty = const "#<forall>" (tyarrow [ty ; propty] propty)     in
  let k_exists ty = const "#<exists>" (tyarrow [ty ; propty] propty)     in
  let k_nabla ty  = const "#<nabla>"  (tyarrow [ty ; propty] propty)     in
  let k_eq ty     = const "#<eq>"     (tyarrow [ty ; ty] propty)         in
  let k_aobj      = const "#<aobj>"   (tyarrow [olistty] propty)         in
  let k_sobj      = const "#<sobj>"   (tyarrow [olistty] propty)         in
  let k_pred      = const "#<pred>"   (tyarrow [oty] propty)             in
  let open Metaterm in
  let rec metaterm = function
    | True -> k_true
    | False -> k_false
    | And (f, g) -> app k_and [metaterm f ; metaterm g]
    | Or (f, g) -> app k_or [metaterm f ; metaterm g]
    | Arrow (f, g) -> app k_arrow [metaterm f ; metaterm g]
    | Binding (_, [], f) -> metaterm f
    | Binding (q, ((x, xty) :: bs), f) ->
        let kq = match q with
          | Forall -> k_forall xty
          | Exists -> k_exists xty
          | Nabla -> k_nabla xty
        in
        let mt = replace_metaterm_vars [x, db 1] (Binding (q, bs, f)) in
        app kq [lambda [x, xty] (metaterm mt)]
    | Eq (s, t) -> app (k_eq (tc [] s)) [s ; t]
    | Obj (obj, _) -> begin
        match obj.mode with
        | Async ->
            app k_aobj [context obj.context ; obj.right]
        | Sync foc ->
            app k_sobj [context obj.context ; foc ; obj.right]
      end
    | Pred (p, _) -> app k_pred [p]
  and context = function
    | [] -> const Typing.k_nil olistty
    | t :: ts -> app (const Typing.k_cons (tyarrow [oty ; olistty] olistty)) [t ; context ts]
  in
  metaterm

let horpo_metaterms ms0 mt0 =
  let s0 = metaterm_inject ms0 in
  let t0 = metaterm_inject mt0 in
  horpo s0 t0

let extend_ctx cx1 cx2 =
  List.fold_left begin fun (cx, sub) (x, ty) ->
    let xx = fresh_name x cx in
    let cx = (xx, ty) :: cx in
    let sub = (x, const xx ty) :: sub in
    (cx, sub)
  end (cx1, []) cx2

let stratification_check ~def =
  let nocc : (tyctx * term list) list ref = ref [] in
  let measure t = match term_head t with
    | Some (_, args) -> args
    | None -> bugf "stratification_check#measure"
  in
  let emit cx t = nocc := (cx, measure t) :: !nocc in
  let open Metaterm in
  let rec scan_nocc rt cx a = match a with
    | True | False | Eq _ | Obj _ -> ()
    | And (a, b) | Or (a, b) ->
        scan_nocc rt cx a ;
        scan_nocc rt cx b
    | Arrow (a, b) ->
        scan_nocc false cx a ;
        scan_nocc rt cx b
    | Binding (q, acx, a) ->
        let (cx, sub) = extend_ctx cx acx in
        let a = replace_metaterm_vars sub a in
        scan_nocc rt cx a
    | Pred (p, _) ->
        if Itab.mem (term_head_name p) def.atoms && not rt then emit cx p
  in
  let rec get_head h =
    let (cx, p) = match h with
      | Binding (_, cx, Pred (p, _)) -> (cx, p)
      | Pred (p, _) -> ([], p)
      | _ -> bugf "Bad head"
    in
    (capital_tids [p] @ cx, measure p)
  in
  List.filter_map begin fun cl ->
    let cx, h = get_head cl.head in
    nocc := [] ;
    scan_nocc true cx cl.body ;
    if !nocc = [] then None
    else Some ((cx, h), !nocc)
  end def.clauses

module Test = struct

  let natty = tybase "nat"
  let aty = tybase "A"

  let k_rec = const "rec" (tyarrow [natty ; aty ; tyarrow [natty ; aty] aty] aty)
  let k_zero = const "z" natty
  let k_succ = const "s" (tyarrow [natty] natty)

  let k_u = const "u" aty
  let k_X = const "X" (tyarrow [natty ; aty] aty)

  let r1l = app k_rec [k_zero ; k_u ; k_X]
  let r1r = k_u

  let r2l = app k_rec [app k_succ [const "x" natty] ; k_u ; k_X]
  let r2r = app k_X [const "x" natty ; app k_rec [const "x" natty ; k_u ; k_X]]

  let r3l = lambda ["x", natty] (app k_rec [app k_succ [db 1] ; k_u ; k_X])
  let r3r = lambda ["x", natty] (app k_X [db 1 ; app k_rec [db 1 ; k_u ; k_X]])

  let tyty = tybase "ty"
  let k_arrow = const "arrow" (tyarrow [tyty ; tyty] tyty)
  let k_a = const "A" tyty
  let k_b = const "B" tyty
  let k_ab = app k_arrow [k_a ; k_b]
  let k_aa = app k_arrow [k_a ; k_a]

end
