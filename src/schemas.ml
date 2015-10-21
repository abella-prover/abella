(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)
(* Schemas *)

open Term
open Typing
open Metaterm
open Format
open Tactics
open Prover
open Abella_types
open Extensions

module H = Hashtbl

let schemas : (string, term schema) Hashtbl.t = State.table ()

let type_block bl =
  let eqns = ref [] in
  let tyctx = bl.bl_nabla in
  let esign =
    let basics, consts = !sign in
    (basics, List.map (fun (v, ty) -> (v, Poly ([], ty))) (bl.bl_exists @ bl.bl_nabla) @ consts) in
  List.iter begin fun rel ->
    List.iter begin fun elem ->
      eqns := snd (Typing.infer_type_and_constraints ~sign:esign tyctx elem) @ !eqns
    end rel
  end bl.bl_rel ;
  let sub = Typing.unify_constraints !eqns in
  let bl_exists = Typing.apply_sub_tyctx sub bl.bl_exists in
  let bl_nabla = Typing.apply_sub_tyctx sub bl.bl_nabla in
  List.iter (Typing.tid_ensure_fully_inferred ~sign:!sign) bl_exists ;
  List.iter (Typing.tid_ensure_fully_inferred ~sign:!sign) bl_nabla ;
  let bl_rel = List.map begin fun rel ->
      List.map begin fun elem ->
        Typing.uterm_to_term sub elem
      end rel
    end bl.bl_rel in
  {bl_exists ; bl_nabla ; bl_rel}

let format_schema ff sch =
  let open Format in
  pp_open_vbox ff 2 ; begin
    pp_print_string ff "Schema " ;
    pp_print_string ff sch.sch_name ;
    pp_print_string ff " := " ;
    List.iter begin fun bl ->
      pp_print_cut ff () ;
      pp_open_box ff 2 ; begin
        if bl.bl_exists <> [] then begin
          pp_print_string ff "exists " ;
          pp_open_box ff 0 ; begin
            List.iter_sep ~sep:(pp_print_space ff) begin fun (v, ty) ->
              fprintf ff "(%s:%s)" v (ty_to_string ty)
            end bl.bl_exists ;
          end ; pp_close_box ff () ;
          pp_print_string ff "," ;
          if bl.bl_nabla <> [] then pp_print_space ff () ;
        end ;
        if bl.bl_nabla <> [] then begin
          pp_print_string ff "nabla " ;
          pp_open_box ff 0 ; begin
            List.iter_sep ~sep:(pp_print_space ff) begin fun (v, ty) ->
              fprintf ff "(%s:%s)" v (ty_to_string ty)
            end bl.bl_nabla ;
          end ; pp_close_box ff () ;
          pp_print_string ff "," ;
        end ;
        pp_print_space ff () ;
        pp_print_string ff "(" ;
        pp_open_box ff 2 ; begin
          List.iter_sep ~sep:(fun () -> fprintf ff ",@ ") begin fun rel ->
            if rel = [] then pp_print_string ff k_nil else
              List.iter_sep ~sep:(fun () -> fprintf ff " ::@ ") begin fun elem ->
                format_term ff elem
              end rel
          end bl.bl_rel
        end ; pp_close_box ff () ;
        pp_print_string ff ")" ;
      end ; pp_close_box ff ()
    end sch.sch_blocks ;
  end ; pp_close_box ff ()

let schema_to_defs ?ty sch =
  let pred = Term.const sch.sch_name sch.sch_ty in
  let mk args = Metaterm.pred (Term.app pred args) in
  let k_nil = Term.const k_nil olistty in
  let nil_head = List.range 1 sch.sch_arity |>
                   List.map (fun _ -> k_nil) |> mk in
  let nil_clause = {head = nil_head ; body = True} in
  let k_cons = Term.const k_cons (tyarrow [oty ; olistty] olistty) in
  let block_to_clause bl =
    let rec name_gs gs used = function
      | 0 -> List.rev gs
      | n ->
          let (g, used) = Term.fresh_wrt ~ts:0 Term.Constant "G" olistty used in
          name_gs (g :: gs) used (n - 1)
    in
    let used = ("G", Term.const "G" olistty) :: List.map begin fun (v, ty) ->
        (v, Term.const v ty)
      end bl.bl_exists in
    let gs = name_gs [] used sch.sch_arity in
    let body = mk gs in
    let cons s t = Term.app k_cons [s ; t] in
    let grels = List.combine bl.bl_rel gs |>
                List.map (fun (l, g) -> List.fold_right cons l g) in
    let head = nabla bl.bl_nabla (mk grels) in
    {head ; body}
  in
  let clauses = nil_clause :: List.map block_to_clause sch.sch_blocks in
  (ty, clauses)

let k_member = Term.const k_member (tyarrow [oty ; olistty] propty)
let member x l = pred (Term.app k_member [x ; l])

let schema_invert gs e ~sch comp =
  if comp < 0 || comp >= sch.sch_arity then failwith "schema_invert" ;
  let bindings = (e, oty) :: List.map (fun g -> (g, olistty)) gs in
  let e = Term.const e oty in
  let gs = List.map (fun g -> Term.const g olistty) gs in
  let used = List.map term_to_pair (e :: gs) in
  let block_desc bl =
    let l = List.nth bl.bl_rel comp in
    let occ_vars = find_var_refs Constant l |>
                   List.map term_to_name |>
                   Iset.of_list in
    let bl_exists = List.filter (fun (x, _) -> Iset.mem x occ_vars) bl.bl_exists in
    let bl_nabla = List.filter (fun (x, _) -> Iset.mem x occ_vars) bl.bl_nabla in
    let (xxs, used) = List.fold_left begin fun (xxs, used) (x, xty) ->
        let (xx, used) = fresh_wrt ~ts:0 Constant x xty used in
        (xx :: xxs, used)
      end ([], used) bl_exists in
    let xxs = List.rev xxs in
    let xxsub = List.map2 (fun (x, _) xx -> (x, xx)) bl_exists xxs in
    let (uus, uusub) = List.fold_left begin fun (uus, used) (u, uty) ->
        let (uu, used) = fresh_wrt ~ts:0 Constant u uty used in
        (uu :: uus, used)
      end ([], used) bl_nabla in
    let uus = List.rev uus in
    let sub = xxsub @ uusub in
    let elem_desc f =
      let f = replace_term_vars sub f in
      Eq (e, f) in
    let fresh_evs = List.map (fun u -> List.map (fun x -> (u, x)) xxs) uus
                    |> List.flatten in
    let rec mk_fresh_uus seen = function
      | [] -> List.rev seen
      | u :: uus ->
          let seen = List.rev_map (fun v -> (u, v)) uus @ seen in
          mk_fresh_uus seen uus
    in
    let fresh_uus = mk_fresh_uus [] uus in
    let fresh = List.map begin fun (u, x) ->
        let uty = tc [] u in
        let xty = tc [] x in
        app (const k_fresh (tyarrow [uty ; xty] propty)) [u ; x]
        |> pred
      end (fresh_evs @ fresh_uus) in
    let fresh = match uus, xxs with
      | (_ :: _), [] ->
          let u = List.last uus in
          fresh @ [pred (app (const k_name (tyarrow [tc [] u] propty)) [u])]
      | _ -> fresh in
    let ebindings =
      List.map (fun v -> (term_to_name v, tc [] v)) (xxs @ uus)
    in
    Metaterm.exists ebindings begin
      (List.map elem_desc l |> disjoin) :: fresh |> conjoin
    end
  in
  forall bindings begin
    Arrow (pred (Term.app (Term.const sch.sch_name sch.sch_ty) gs),
           Arrow (member e (List.nth gs comp),
                  List.map block_desc sch.sch_blocks |> disjoin))
  end

let register_typed_schema sch =
  if Hashtbl.mem schemas sch.sch_name then
    failwithf "Schema %S already defined" sch.sch_name ;
  Hashtbl.add schemas sch.sch_name sch ;
  (* Format.printf "%a.@." format_schema sch ; *)
  let (ty, clauses) = schema_to_defs sch in
  add_global_consts [sch.sch_name, sch.sch_ty] ;
  add_defs [] [sch.sch_name, sch.sch_ty] Inductive clauses ;
  let gs = List.range 1 sch.sch_arity |>
           List.map (fun n -> "G" ^ string_of_int n) in
  List.range 0 (sch.sch_arity - 1) |>
  List.map (schema_invert gs "E" ~sch) |>
  List.iteri begin fun i mt ->
    let name = sch.sch_name ^ "_invert" ^ string_of_int (i + 1) in
    add_lemma name [] mt ;
    print_theorem name ([], mt)
  end

let register_schema sch =
  let sch = {sch with sch_blocks = List.map type_block sch.sch_blocks} in
  register_typed_schema sch
