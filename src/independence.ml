open Term
open Typing
open Metaterm
open Format
open Tactics
open Checks
open Abella_types
open Extensions
open Prover

module H = Hashtbl

(* Independence *)

type proof = command list
type theorem_proof = string * metaterm * proof
type definition = flavor * tyctx * udef_clause list
type program_element =
  | Definition of definition
  | TheoremProof of theorem_proof
  | SplitTheorem of id

let thm_proof_to_string pf =
  let rec pts_aux lst =
    match lst with
    | [] -> "\n"
    | h::t -> "    " ^ (command_to_string h) ^ ".\n" ^ (pts_aux t)
  in
  let name,thm,commands = pf in
  "Theorem " ^ name ^ ": \n  " ^ (metaterm_to_string thm) ^ ".\n" ^ (pts_aux commands)

let definition_to_string def =
  let rec aux lst =
    match lst with
    | [] -> failwith "Invalid definition:  no clauses"
    | [l,r] -> "  " ^ (umetaterm_to_string l) ^ " := " ^ (umetaterm_to_string r) ^ ".\n\n"
    | (l,r)::t -> "  " ^ (umetaterm_to_string l) ^ " := " ^ (umetaterm_to_string r) ^ ";\n" ^ (aux t)
  in
  let flav, tctx, uclauses = def in
  let name, ty = List.hd tctx in
  let def_start = "Define " ^ name ^ " : " ^ (ty_to_string ty) ^ " by\n" in
  def_start ^ (aux uclauses)

let rec program_to_string prog =
  match prog with
  | [] -> ""
  | (Definition d)::t -> (definition_to_string d) ^ (program_to_string t)
  | (TheoremProof tp)::t -> (thm_proof_to_string tp) ^ (program_to_string t)
  | (SplitTheorem id)::t -> "Split " ^ id ^ ".\n\n" ^ (program_to_string t)

let rec get_head_predicate trm =
  match (observe trm) with
  | Var v -> [var_to_string v]
  | App (t, tlst) ->
     if (is_imp trm) then
       let left, right = extract_imp trm in
       get_head_predicate right
     else if (is_amp trm) then
       let left, right = extract_amp trm in
       (get_head_predicate left) @ (get_head_predicate right)
     else if (is_pi trm) then
       let abs = extract_pi trm in
       get_head_predicate abs
     else
       get_head_predicate t
  | Lam (tctx, t) -> get_head_predicate t
  | _ -> failwith "Invalid clause found in determining head predicate"

let get_body_clauses trm =
  let rec replace_lambdas tctx t =
    match (observe t) with
    | Var v -> t
    | DB i ->
       let id,ty = List.nth tctx (i-1) in
       var Eigen id 0 ty
    | Lam (ctx, tm) -> replace_lambdas (ctx@tctx) tm
    | App (tm, tlst) -> app (replace_lambdas tctx tm) (List.map (fun a -> replace_lambdas tctx a) tlst)
    | _ -> assert false
  in
  let rec build_body_clause_lst trm =
    match (observe trm) with
    | App (t, tlist) ->
       if (is_imp trm) then
         let left, right = extract_imp trm in
         left::(build_body_clause_lst right)
       else if (is_pi trm) then
         let abs = extract_pi trm in
         build_body_clause_lst abs
       else
         [] (*Reached end of body*)
    | Lam (tctx, t) -> build_body_clause_lst (replace_lambdas tctx t)
    | _ -> []
  in
  build_body_clause_lst trm

let rec member trm lst =
  match lst with
  | [] -> false
  | h::t ->
     if (eq trm h) then
       true
     else
       member trm t

let pred_type pred =
  let rec find_type lst =
    match lst with
    | [] -> failwith "Cannot find type:  Given predicate is undefined"
    | (name, Poly (l,ty))::t -> if (name = pred) then
                                  ty
                                else
                                  find_type t
  in
  let _,lst = !sign in
  find_type lst

let rec fresh_in_tyctx lst var =
  match lst with
  | [] -> true
  | (id,ty)::t -> if (id = var) then
                    false
                  else
                    fresh_in_tyctx t var

let rec fresh_in_term tm var =
  match (observe tm) with
  | Var v -> v.name <> var
  | App (tm',tmlst) -> (fresh_in_term tm' var) && (List.fold_left (fun bool t -> bool && (fresh_in_term t var)) true tmlst)
  | Lam (tctx,tm') -> (fresh_in_term tm' var) && (fresh_in_tyctx tctx var)
  | Susp (tm',i,j,e) -> (fresh_in_term tm' var) && (List.fold_left
                                                      (fun bool eitem ->
                                                        match eitem with
                                                        | Dum i -> bool
                                                        | Binding (tm,i) -> bool && (fresh_in_term tm var)
                                                      ) true e)
  | _ -> true

let fresh_name_term tm base =
  let _,sign_names = !sign in
  let rec get_name i =
    let name = base ^ (string_of_int i) in
    if (fresh_in_term tm name && fresh_in_tyctx sign_names base) then
      name
    else
      get_name (i + 1)
  in
  if (fresh_in_term tm base && fresh_in_tyctx sign_names base) then
    base
  else
    get_name 0

let fresh_name_term_lst tmlst base =
  let _,sign_names = !sign in
  let fresh_in_lst lst name =
    List.fold_left (fun bool t -> bool && (fresh_in_term t name)) true lst
  in
  let rec get_name i =
    let name = base ^ (string_of_int i) in
    let _,sign_names = !sign in
    if (fresh_in_lst tmlst name && fresh_in_tyctx sign_names base) then
      name
    else
      get_name (i + 1)
  in
  if (fresh_in_lst tmlst base && fresh_in_tyctx sign_names base) then
    base
  else
    get_name 0

let rec fresh_in_uterm ut var =
  match ut with
  | UCon (p,name,ty) -> name <> var
  | ULam (p,name,ty,ut') -> if (name = var) then
                              false
                            else
                              fresh_in_uterm ut' var
  | UApp (p,ut1,ut2) -> (fresh_in_uterm ut1 var) && (fresh_in_uterm ut2 var)

let fresh_name_uterm_lst utmlst base =
  let _,sign_names = !sign in
  let fresh_in_lst lst name =
    List.fold_left (fun bool ut -> bool && (fresh_in_uterm ut name)) true lst
  in
  let rec get_name i =
    let name = base ^ (string_of_int i) in
    if (fresh_in_lst utmlst name && fresh_in_tyctx sign_names base) then
      name
    else
      get_name (i + 1)
  in
  if (fresh_in_lst utmlst base && fresh_in_tyctx sign_names base) then
    base
  else
    get_name 0

let fresh_name_uterm ut base =
  let _,sign_names = !sign in
  let rec get_name i =
    let name = base ^ (string_of_int i) in
    if (fresh_in_uterm ut name && fresh_in_tyctx sign_names base) then
      name
    else
      get_name (i + 1)
  in
  if (fresh_in_uterm ut base && fresh_in_tyctx sign_names base) then
    base
  else
    get_name 0

             
let register_theorem name thm =
  add_lemma name [] thm;
  theorem thm

let finish_proof reason =
  match reason with
  | `completed -> reset_prover ()
  | _ -> failwith "Automated proof not completed"


let strengthen_count = ref 1


let make_ctx_name pred =
  "ctx_" ^ pred ^ (string_of_int !strengthen_count)

let make_subctx_name pred_sub pred_super =
  (make_ctx_name pred_sub) ^ "_subctx_" ^ (make_ctx_name pred_super)

let make_indep_name pred =
  "indep" ^ (string_of_int !strengthen_count) ^ "_" ^ pred

let rec collect_quantified_variables trm =
  let is_constant name =
    let rec find_in_sign name lst =
      match lst with
      | [] -> false
      | (const_name,_)::t -> if (const_name = name) then
                               true
                             else
                               find_in_sign name t
    in
    let _,constants = !sign in
    (H.mem defs_table name) || (find_in_sign name constants)
  in
  let obtm = observe trm in
  match obtm with
  | Var v -> if (is_constant v.name) then
               []
             else
               [(v.name,v.ty)]
  | App (t, tlist) ->
     (collect_quantified_variables t) @ (List.fold_left (fun lst tm -> (collect_quantified_variables tm) @ lst) [] tlist)
  | _ -> []


type set_ref =
  | Ref of id
  | Formula of term

let pred_list : string list ref = ref []


exception StrengthenFailure




let collect_contexts dynamic_contexts all_ctx_terms =
  let ctx_col : (string, set_ref list) H.t = H.create 10 in
  let gamma' = ref (all_ctx_terms @ !clauses) in

  let rec simplify_constraints cnstrnts output =
    let rec add_formulas lst pred =
      match lst with
      | [] -> false
      | h::t ->
         match h with
         | Formula trm ->
            if not (member trm (H.find output pred)) then
              let _ = H.replace output pred (trm::(H.find output pred)) in
              let _ = add_formulas t in
              true
            else
              add_formulas t pred
         | Ref s ->
            if ((H.mem cnstrnts s) && s <> pred) then
              add_formulas ((H.find cnstrnts s) @ t) pred
            else
              add_formulas t pred

    in
    let rec simplify_iterate lst changed =
      match lst with
      | [] -> changed
      | h::t -> simplify_iterate t ((add_formulas (H.find cnstrnts h) h) || changed)

    in
    let rec simplify_aux () =
      if (simplify_iterate !pred_list false) then
        simplify_aux ()
      else
        ()

    in
    List.iter (fun h -> if (not (H.mem cnstrnts h)) then (*add empty context constraints*)
                          H.add cnstrnts h []
              ) !pred_list;
    simplify_aux ()

  in
  let add_constraints trm =
    let head_pred_trm = get_head_predicate trm in
    let body_trm = get_body_clauses trm in
    let rec go_through_body body =
      match body with
      | [] -> ()
      | g_i::t ->
         let head_predicates_g_i = get_head_predicate g_i in
         let body_g_i = get_body_clauses g_i in
         let _ = go_through_body t in
         let _ = gamma' := body_g_i @ !gamma' in
         List.iter (fun hp_g_i ->
             if H.mem ctx_col hp_g_i then
               H.replace ctx_col hp_g_i ((List.map (fun p -> Ref p) (List.filter (fun s -> s <> hp_g_i) head_pred_trm)) @
                                           (List.map (fun t -> Formula t) body_g_i) @
                                             (H.find ctx_col hp_g_i))
             else
               H.add ctx_col hp_g_i ((List.map (fun p -> Ref p) (List.filter (fun s -> s <> hp_g_i) head_pred_trm)) @
                                       (List.map (fun t -> Formula t) body_g_i))
           ) head_predicates_g_i
    in go_through_body body_trm

  in
  while !gamma' <> [] do
    match !gamma' with
    | h::t -> gamma' := t; add_constraints h
    | [] -> ()
  done;

  let extract_all_predicates () =
    let rec collect_preds lst =
      match lst with
      | [] -> []
      | (pred,Poly (_,ty))::tl ->
         if (pred = "=>" || pred = "&") then (*don't add built-in predicates*)
           collect_preds tl
         else if (ty = oty) then
           pred::(collect_preds tl)
         else
           match ty with
           (*match higher-order types*)
           | Ty ([Ty ([x],_)],_) -> collect_preds tl
           (*match type prediates*)
           | Ty (lst,bty) ->
              if ((tybase bty) = oty) then
                pred::(collect_preds tl)
              else
                collect_preds tl
    in
    let _,l = !sign in
    collect_preds l
            
  in
  pred_list := extract_all_predicates ();
  List.iter (fun h -> H.add dynamic_contexts h all_ctx_terms) !pred_list; (*add to all contexts*)
  simplify_constraints ctx_col dynamic_contexts




let collect_dependencies dynamic_contexts dependencies =
  let dep_col = H.create 10 in
  let gamma' = !clauses in

  let simplify_constraints cnstrnts output =
    let rec add_dependencies lst pred =
      match lst with
      | [] -> false
      | dep_pred::tail ->
         let changed = List.fold_right (fun p changed ->
                           if (not (List.mem p (H.find output pred))) then
                             let _ = H.replace output pred (p::(H.find output pred)) in
                             true
                           else
                             changed) (H.find output dep_pred) false in
         (add_dependencies tail pred) || changed
                                           
    in
    let rec simplify_aux () =
      let a = List.fold_right (fun h changed ->
                  (add_dependencies (H.find cnstrnts h) h) || changed) !pred_list false in
      if (a) then
        simplify_aux ()
      else
        ()
          
    in
    List.iter (fun h -> H.add output h [h]) !pred_list;
    simplify_aux ()
                 
  in
  let add_constraints (pred : string) =
    let find_matching_preds cl lst =
      match lst with
      | [] -> ()
      | h::t ->
         if (h = pred) then
           let body = get_body_clauses cl in
           List.iter (fun trm ->
               let head_preds = get_head_predicate trm in
               List.iter (fun head ->
                   if (List.mem head (H.find dep_col pred)) then
                     ()
                   else
                     H.replace dep_col pred (head::(H.find dep_col pred))
                 ) head_preds
             ) body
                     
    in
    let aux lst =
      List.iter (fun cl ->
          let head_predicates = get_head_predicate cl in
          find_matching_preds cl head_predicates
        ) lst
    in
    H.add dep_col pred [];
    aux gamma';
    aux (H.find dynamic_contexts pred)
        
  in
  List.iter (fun pred -> add_constraints pred) !pred_list;
  simplify_constraints dep_col dependencies




(*Prove g independent of f*)
let independent f g dynamic_contexts dependencies =

  let rec make_variables_universal trm =
    match (observe trm) with
    | Var v -> if (v.tag = Constant) then
                 trm
               else
                 var v.tag (String.uppercase v.name) v.ts v.ty
    | App (t, tlist) -> app (make_variables_universal t) (List.map make_variables_universal tlist)
    | _ -> trm
             
  in
  
  let rec term_to_uterm trm =
    match (observe trm) with
    | Var v -> UCon ((Lexing.dummy_pos,Lexing.dummy_pos), v.name, v.ty)
    | App (tm1,[tm2]) -> UApp ((Lexing.dummy_pos,Lexing.dummy_pos), term_to_uterm tm1, term_to_uterm tm2)
    | App (tm, tlst) -> List.fold_left (fun ut t ->
                            let x = term_to_uterm t in
                            UApp ((Lexing.dummy_pos,Lexing.dummy_pos), ut, x)) (term_to_uterm tm) tlst
    | _ -> bugf "Should not have any terms but Vars and Apps"

  in
  let define_ctx pred =
    let ctx_formulas = H.find dynamic_contexts pred in
    let ctx_name = make_ctx_name pred in
    let rec add_formula form_lst =
      match form_lst with
      | [] -> []
      | h::t -> 
         let cap_term = make_variables_universal h in
         let ctx_var = fresh_name_term cap_term "L" in
         let l = add_formula t in
         let def = UPred (UApp ((Lexing.dummy_pos,Lexing.dummy_pos),
                                UCon ((Lexing.dummy_pos,Lexing.dummy_pos),
                                      ctx_name, (tyarrow [olistty] propty)),
                                UApp ((Lexing.dummy_pos,Lexing.dummy_pos),
                                      UApp ((Lexing.dummy_pos,Lexing.dummy_pos),
                                            UCon ((Lexing.dummy_pos,Lexing.dummy_pos),
                                                  "::", (tyarrow [oty; olistty] olistty)),
                                            term_to_uterm cap_term),
                                      UCon ((Lexing.dummy_pos,Lexing.dummy_pos),
                                            ctx_var, olistty))), Irrelevant) in
         let def_proof = UPred (UApp ((Lexing.dummy_pos,Lexing.dummy_pos),
                                      UCon ((Lexing.dummy_pos,Lexing.dummy_pos),
                                            ctx_name, (tyarrow [olistty] propty)),
                                      UCon ((Lexing.dummy_pos,Lexing.dummy_pos),
                                            ctx_var, olistty)),
                                Irrelevant) in
         (def,def_proof)::l
    in
    let rec build_mem_thm form_lst mem_var =
      let rec other_to_const tm =
        match (observe tm) with
        | Var v -> if (v.tag == Constant) then
                     tm
                   else
                     var Constant v.name v.ts v.ty
        | App (t1,tl) -> app (other_to_const t1) (List.map other_to_const tl)
        | Lam (tctx,t) -> lambda tctx (other_to_const t)
        | _ -> tm
      in
      match form_lst with
      | [] -> False
      | [h] ->
         let quant_vars = collect_quantified_variables h in
         let mtm_quantifications = (if ((List.length quant_vars) > 0) then
                                      Binding (Exists,
                                               List.fold_right (fun x l -> x::l) quant_vars [],
                                               Eq (var Constant mem_var 0 oty, other_to_const h))
                                    else
                                      Eq (var Constant mem_var 0 oty, h)
                                   ) in
         mtm_quantifications
      | h::t ->
         let quant_vars = collect_quantified_variables h in
         let mtm_quantifications =
           (if ((List.length quant_vars) > 0) then
              Binding (Exists,
                       List.fold_right (fun x l -> x::l) quant_vars [],
                       Eq (var Constant mem_var 0 oty, other_to_const h))
            else
              Eq (var Constant mem_var 0 oty, h)
           ) in
         let mtm = build_mem_thm t mem_var in
         Or (mtm_quantifications, mtm)
    in
    let rec add_proof_step form_lst prf_lst =
      match form_lst with
      | [] -> prf_lst
      | h::t ->
         let () = case (Remove ("H2", [])) in
         let prf_lst = (Case (Remove ("H2",[]), None))::prf_lst in
         let () = search ~witness:WMagic ~handle_witness:(fun x -> ()) () in
         let prf_lst = (Search `nobounds)::prf_lst in
         let () = apply (Keep ("IH",[])) [(Keep ("H3",[])); (Keep ("H4",[]))] [] in
         let prf_lst = (Apply (None, Keep ("IH",[]), [(Keep ("H3",[])); (Keep ("H4",[]))], [], None))::prf_lst in
         let () = (
             try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
             | Prover.End_proof reason -> finish_proof reason
           ) in
         let prf_lst = (Search `nobounds)::prf_lst in
         add_proof_step t prf_lst
    in
    let rec add_grown_context_lemma form_lst index =
      match form_lst with
      | [] -> []
      | h::t ->
         let thm_name = ctx_name ^ "_plus" ^ (string_of_int index) in
         let thm1 = Pred (app (var Constant ctx_name 0 (tyarrow [olistty] propty))
                              [var Constant "L" 0 olistty],
                          Irrelevant) in
         let thm2 = Pred (app (var Constant ctx_name 0 (tyarrow [olistty] propty))
                              [app (var Constant "::" 0 (tyarrow [oty; olistty] olistty))
                                   [h; var Constant "L" 0 olistty]],
                          Irrelevant) in
         let quant_vars = collect_quantified_variables h in
         let thm = Binding (Forall, ("L",olistty)::quant_vars, Arrow (thm1, thm2)) in
         let () = register_theorem thm_name thm in
         let () = (
             try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
             | Prover.End_proof reason -> finish_proof reason
           ) in
         let proof_lst = add_grown_context_lemma t (index + 1)in
         (TheoremProof (thm_name,thm,[Search `nobounds]))::proof_lst
    in

    let ctx_type = tyarrow [olistty] propty in
    let defs = add_formula ctx_formulas in
    let full_defs = (UPred (UApp ((Lexing.dummy_pos,Lexing.dummy_pos),
                                  UCon ((Lexing.dummy_pos,Lexing.dummy_pos),
                                        ctx_name, (tyarrow [olistty] propty)),
                                  UCon ((Lexing.dummy_pos,Lexing.dummy_pos),
                                        "nil", olistty)), Irrelevant),
                     UTrue)::defs in
    let def = Define (Inductive, [(ctx_name,ctx_type)], full_defs) in
    let program_definition = Definition (Inductive, [ctx_name,ctx_type], full_defs) in
    let _ = register_definition def in

    let gc_proof_lsts = add_grown_context_lemma ctx_formulas 1 in

    let ctx_var = fresh_name_term_lst ctx_formulas "L" in
    let mem_var = fresh_name_term_lst ctx_formulas "E" in
    let thm_name = ctx_name ^ "_mem" in
    let mtm = build_mem_thm ctx_formulas mem_var in
    let thm_1 = Pred (app (var Constant ctx_name 0 (tyarrow [olistty] propty))
                          [var Constant ctx_var 0 olistty],
                      Irrelevant) in
    let thm_2 = Pred (app (var Constant "member" 0 (tyarrow [oty; olistty] propty))
                          [var Constant mem_var 0 oty; var Constant ctx_var 0 olistty],
                      Irrelevant) in
    if (List.length ctx_formulas > 0) then
      let thm = Binding (Forall, [(ctx_var,olistty); (mem_var,oty)], Arrow (thm_1, Arrow (thm_2, mtm))) in
      let _ = register_theorem thm_name thm in
      let () = induction [1] in
      let () = intros [] in
      let () = case (Remove ("H1", [])) in
      let () = case (Keep ("H2", [])) in
      let proof_lst = add_proof_step ctx_formulas [] in
      let proof_lst = (Induction ([1],None))::(Intros [])::(Case (Remove ("H1",[]),None))::
                        (Case (Keep ("H2",[]),None))::List.rev proof_lst in
      program_definition::(TheoremProof (thm_name, thm, proof_lst))::gc_proof_lsts
    else
      let thm = Binding (Forall, [(ctx_var,olistty); (mem_var,oty)], Arrow (thm_1, Arrow (thm_2, False))) in
      let _ = register_theorem thm_name thm in
      let () = induction [1] in
      let () = intros [] in
      let () = case (Remove ("H1", [])) in
      let () = (try case (Keep ("H2", [])) with
                | Prover.End_proof reason -> finish_proof reason
               ) in
      let proof_structure = TheoremProof (thm_name, thm,
                                          [Induction ([1],None); Intros []; Case (Remove ("H1",[]),None);
                                           Case (Keep ("H2",[]),None)]) in
      program_definition::proof_structure::gc_proof_lsts

  in
  let subctx_thm subp pred subp_ctx =
    let rec add_step lst prf_lst =
      match lst with
      | [] -> prf_lst
      | h::t ->
         let () = apply (Keep ("IH",[])) [(Keep ("H2",[]))] [] in
         let () = (
             try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
             | Prover.End_proof reason -> finish_proof reason
           ) in
         let prf_lst = (Search `nobounds)::(Apply (None, Keep ("IH",[]), [Keep ("H2",[])], [], None))::prf_lst in
         add_step t prf_lst
    in
    let subctx_name = make_subctx_name subp pred in
    let subp_ctx_name = make_ctx_name subp in
    let pred_ctx_name = make_ctx_name pred in
    let umtm1 = Pred (app (var Constant subp_ctx_name 0 (tyarrow [olistty] propty))
                          [var Constant "L" 0 olistty],
                      Irrelevant) in
    let umtm2 = Pred (app (var Constant pred_ctx_name 0 (tyarrow [olistty] propty))
                          [var Constant "L" 0 olistty],
                      Irrelevant) in
    let thm = Binding (Forall, [("L",olistty)], Arrow (umtm1, umtm2)) in
    let () = register_theorem subctx_name thm in
    let () = induction [1] in
    let () = intros [] in
    let () = case (Remove ("H1", [])) in
    let () = (
        try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
        | Prover.End_proof reason -> finish_proof reason
      ) in
    let prf_lst = add_step subp_ctx [] in
    let prf_lst = (Induction ([1],None))::(Intros [])::(Case (Remove ("H1",[]),None))::
                    (Search `nobounds)::(List.rev prf_lst) in
    TheoremProof (subctx_name, thm, prf_lst)

  in
  let indep_theorem g_dep =
    let rec build_theorem dep_lst f_quant_vars =
      match dep_lst with
      | [] -> failwith "Found empty dependency list"
      | [h] ->
         let ctx_name = make_ctx_name h in
         let h_ty = pred_type h in
         let h_arg_tys = (match h_ty with
                          | Ty (tylst, bty) -> tylst) in
         let h_var_tm = var Constant h 0 h_ty in
         let h_tm_args,h_quant_vars = List.fold_left
                                        (fun (tmlst,vars) ty ->
                                          let name = fresh_name_term_lst (h_var_tm::f::tmlst) "X" in
                                          ((var Constant name 0 ty)::tmlst, (name,ty)::vars)
                                        )
                                        ([], []) h_arg_tys in
         let h_tm = app h_var_tm h_tm_args in
         let ctx_var = fresh_name_term f "L" in
         let universally_quantified_vars = (ctx_var, olistty)::(f_quant_vars @ h_quant_vars) in
         let umtm1 = Pred (app (var Constant ctx_name 0 (tyarrow [olistty] propty))
                               [var Constant ctx_var 0 olistty],
                           Irrelevant) in
         let f = let rec replace_in_with f name repl =
                   match (observe f) with
                   | Var v -> if (v.name = name) then
                                repl
                              else
                                observe f
                   | App (t1, tl) -> app (replace_in_with t1 name repl)
                                         (List.map (fun t2 -> replace_in_with t2 name repl) tl)
                   | _ -> f
                 in List.fold_left (fun y (h,ty) -> replace_in_with y h (var Constant h 0 ty)) f f_quant_vars in
         let umtm2 = Obj ({context = [var Constant ctx_var 0 olistty; f];
                           right = h_tm;
                           mode = Async;}, Irrelevant) in
         let umtm3 = Obj ({context = [var Constant ctx_var 0 olistty];
                              right = h_tm;
                              mode = Async;}, Irrelevant) in
         let this_dep_interior = Arrow (umtm1, Arrow (umtm2, umtm3)) in
         let this_dep = Binding (Forall, universally_quantified_vars, this_dep_interior) in
         this_dep
      | h::t ->
         let ctx_name = make_ctx_name h in
         let h_ty = pred_type h in
         let h_arg_tys = (match h_ty with
                          | Ty (tylst, bty) -> tylst) in
         let h_var_tm = var Constant h 0 h_ty in
         let h_tm_args,h_quant_vars = List.fold_left
                                        (fun (tmlst,vars) ty ->
                                          let name = fresh_name_term_lst (h_var_tm::f::tmlst) "X" in
                                          ((var Constant name 0 ty)::tmlst, (name,ty)::vars)
                                        )
                                        ([], []) h_arg_tys in
         let h_tm = app h_var_tm h_tm_args in
         let ctx_var = fresh_name_term f "L" in
         let universally_quantified_vars = (ctx_var, olistty)::(f_quant_vars @ h_quant_vars) in
         let rest_of_thm = build_theorem t f_quant_vars in
         let umtm1 = Pred (app (var Constant ctx_name 0 (tyarrow [olistty] propty))
                               [var Constant ctx_var 0 olistty],
                           Irrelevant) in
         let f = let rec replace_in_with f name repl =
                   match (observe f) with
                   | Var v -> if (v.name = name) then
                                repl
                              else
                                observe f
                   | App (t1, tl) -> app (replace_in_with t1 name repl)
                                         (List.map (fun t2 -> replace_in_with t2 name repl) tl)
                   | _ -> f
                 in List.fold_left (fun y (h,ty) -> replace_in_with y h (var Constant h 0 ty)) f f_quant_vars in
         let umtm2 = Obj ({context = [var Constant ctx_var 0 olistty; f];
                           right = h_tm;
                           mode = Async;}, Irrelevant) in
         let umtm3 = Obj ({context = [var Constant ctx_var 0 olistty];
                              right = h_tm;
                              mode = Async;}, Irrelevant) in
         let this_dep_interior = Arrow (umtm1, Arrow (umtm2, umtm3)) in
         let this_dep = Binding (Forall, universally_quantified_vars, this_dep_interior) in
         And (this_dep, rest_of_thm)
    in
    let build_proof g_dep =
      let find_ih dep p =
        let rec find_aux lst =
          match lst with
          | [] -> bugf "Did not find dependency in dependency list"
          | h::t -> if (h = p) then
                      0
                    else
                      (find_aux t) + 1
        in
        let ind = find_aux dep in
        if (ind = 0) then
          "IH"
        else
          "IH" ^ (string_of_int ind)
      in
      let get_antecedents trm =
        let rec remove_pis tm =
          if (is_pi tm) then
            let abs = extract_pi tm in
            let base = (match (observe abs) with
                        | Lam (_, tm) -> tm
                        | _ -> abs) in
            remove_pis base
          else
            tm
        in
        let rec antecedent_aux trm =
          let ob_tm = observe trm in
          match ob_tm with
          | Var  v -> [ob_tm]
          | App  (t,tlst) -> if (is_imp ob_tm) then
                               let a,b = extract_imp ob_tm in
                               let lst = antecedent_aux b in
                               a::lst
                             else
                               [ob_tm]
          | _ -> failwith "Term should not contain anything but Var and App"
        in
        let rec remove_last lst =
          match lst with
          | [] -> []
          | [x] -> []
          | h::t -> h::(remove_last t)
        in
        let trm = remove_pis trm in
        if (is_imp trm) then
          remove_last (antecedent_aux trm)
        else
          []
      in
      let iterate_antecedents pred lst index prf_lst =
        let apply_ind_hyp tm hyp_ind ctx_hyp_ind prf_lst =
          let find_gc_lemma tm head =
            let rec find_aux lst i =
              match lst with
              | [] -> bugf "Dynamic context member not found in dynamic context"
              | h::t -> if eq tm h then
                          i
                        else
                          find_aux t (i + 1)
            in
            let lst = H.find dynamic_contexts head in
            (make_ctx_name head) ^ "_plus" ^ (string_of_int (find_aux lst 1))
          in
          let rec iter_grown_ctx lst head index prf_lst =
            match lst with
            | [] -> index, prf_lst
            | h::t ->
               let ctx_plus_name = find_gc_lemma h head in
               let hyp_name = "H" ^ (string_of_int index) in
               let () = apply (Keep (ctx_plus_name,[])) [Keep (hyp_name,[])] [] in
               let prf_lst = (Apply (None, Keep (ctx_plus_name,[]), [Keep (hyp_name,[])], [], None))::prf_lst in
               let max_index, prf_lst = iter_grown_ctx t head (index + 1) prf_lst in
               max_index, prf_lst
          in
          let head = List.hd (get_head_predicate tm) in
          let subctx_lemma = make_subctx_name pred head in
          let () = apply (Keep (subctx_lemma,[])) [Keep ("H1",[])] [] in
          let grown_ctx = get_antecedents tm in
          let last_ctx_ind, proof_lst = iter_grown_ctx grown_ctx head ctx_hyp_ind
                                            ((Apply (None, Keep (subctx_lemma,[]), [Keep ("H1",[])], [], None))::
                                               prf_lst) in
          let ih = find_ih g_dep head in
          let ctx_hyp = "H" ^ (string_of_int last_ctx_ind) in
          let pred_hyp = "H" ^ (string_of_int hyp_ind) in
          let () = apply (Keep (ih, [])) [Keep (ctx_hyp, []); Keep (pred_hyp, [])] [] in
          let proof_lst = (Apply (None, Keep (ih,[]), [Keep (ctx_hyp,[]); Keep (pred_hyp,[])], [], None))::proof_lst in
          proof_lst
        in

        let rec aux lst index ctx_hyp_ind prf_lst =
          match lst with
          | [] -> prf_lst
          | h::t ->
             let proof_lst = apply_ind_hyp h index ctx_hyp_ind prf_lst in
             let proof_lst = aux t (index + 1) (ctx_hyp_ind + 2) proof_lst in
             proof_lst
        in aux lst index (index + (List.length lst)) prf_lst

      in
      let rec build_reg_ctx_prf pred lst prf_lst =
        match lst with
        | [] -> prf_lst
        | h::t ->
           if ((get_head_predicate h) = [pred]) then
             let antecedents = get_antecedents h in
             let proof_lst = iterate_antecedents pred antecedents 3 prf_lst in
             let () = search ~witness:WMagic ~handle_witness:(fun x -> ()) () in
             build_reg_ctx_prf pred t ((Search `nobounds)::proof_lst)
           else
             build_reg_ctx_prf pred t prf_lst
      in
      let build_dyn_ctx_prf pred prf_lst =
        let rec iterate_ctx pred obj_hyp_index lst prf_lst =
          match lst with
          | [] -> prf_lst
          | h::t ->
             let () = (try case (Remove ("H3", [])) with
                       | Prover.End_proof reason -> finish_proof reason
                      ) in
             let proof_lst = (Case (Remove ("H3",[]),None))::prf_lst in
             if ((get_head_predicate h) = [pred]) then
               let antecedents = get_antecedents h in
               let proof_lst = iterate_antecedents pred antecedents obj_hyp_index proof_lst in
               let () = (try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
                         | Prover.End_proof reason -> finish_proof reason
                        ) in
               iterate_ctx pred obj_hyp_index t ((Search `nobounds)::proof_lst)
             else
               iterate_ctx pred obj_hyp_index t proof_lst
        in
        let rec iter_indep lst index prf_lst =
          match lst with
          | [] -> prf_lst
          | h::t ->
             let mem_hyp = "H" ^ (string_of_int index) in
             let () = case (Remove (mem_hyp, [])) in
             let () = case (Remove ("H3", [])) in
             let proof_lst = (Case (Remove ("H3",[]),None))::(Case (Remove (mem_hyp,[]),None))::prf_lst in
             let proof_lst = iter_indep t (index + 2) proof_lst in
             proof_lst
        in
        let proof_lst = iter_indep [f] 4 prf_lst in
        let ctx_mem_name = (make_ctx_name pred) ^ "_mem" in
        let () = (try apply (Keep (ctx_mem_name,[])) [(Keep ("H1",[])); (Keep ("H5",[]))] [] with
                  | Prover.End_proof reason ->
                     finish_proof reason
                 )in
        let proof_lst = (Apply (None, Keep (ctx_mem_name,[]), [Keep ("H1",[]); Keep ("H5",[])], [], None))::proof_lst in
        let ctx_formulas = H.find dynamic_contexts pred in
        let obj_hyp_index,proof_lst = (if ((List.length ctx_formulas) > 1) then
                                         let mem_eq_hyp = "H" ^ (string_of_int 6) in
                                         let () = case (Remove (mem_eq_hyp,[])) in
                                         let proof_lst = (Case (Remove (mem_eq_hyp,[]),None))::proof_lst in
                                         7, proof_lst
                                       else
                                         6, proof_lst) in
        let proof_lst = iterate_ctx pred obj_hyp_index ctx_formulas proof_lst in
        proof_lst
      in
      let rec each_pred lst prf_lst =
        match lst with
        | [] ->  prf_lst
        | h::t ->
           let () = intros [] in
           let proof_lst = (Intros [])::prf_lst in
           let () = case  (Remove ("H2", [])) in
           let proof_lst = (Case (Remove ("H2",[]), None))::proof_lst in
           let reg_ctx_prf_lst = build_reg_ctx_prf h !clauses proof_lst in
           let full_prf_lst = build_dyn_ctx_prf h reg_ctx_prf_lst in
           each_pred t full_prf_lst
      in
      let ind_lst = List.map (fun x -> 2) g_dep in
      let () = induction ind_lst in
      let prf_lst = [Induction (ind_lst, None)] in
      if ((List.length g_dep) > 1) then
        let () = split false in
        let prf_lst = Split::prf_lst in
        each_pred g_dep prf_lst
      else
        each_pred g_dep prf_lst
    in
    let indep_name = make_indep_name g in
    let quant_vars = collect_quantified_variables f in
    let mtm = build_theorem g_dep quant_vars in
    let () = register_theorem indep_name mtm in
    let prf_lst = build_proof g_dep in
    TheoremProof (indep_name, mtm, List.rev prf_lst)

  in
  let dep_g = H.find dependencies g in
  let f_head = get_head_predicate f in
  if (List.mem (List.hd f_head) dep_g) then
    failwith ("Cannot prove " ^ g ^ " independent of " ^ (term_to_string f) ^ "--dependency exists");
  let context_theorems = List.fold_right (fun pred lst -> (define_ctx pred) @ lst) dep_g [] in
  let subctxs =  List.fold_right (fun x lst -> let x_ctx = H.find dynamic_contexts x in
                                               let dep_x = H.find dependencies x in
                                               (List.fold_right (fun dep_pred l ->
                                                    (subctx_thm x dep_pred x_ctx)::l) dep_x lst))
                  dep_g [] in
  let independence = indep_theorem dep_g in
  let independence_program = context_theorems @ subctxs @ [independence] in
  independence_program





let strengthen () =
  let rec strip_bindings thm =
    match thm with
    | Binding (_, lst, t) -> strip_bindings t
    | _ -> thm
  in
  let extract_from_theorem thm =
    let plain_thm = strip_bindings thm in
    match plain_thm with
    | Arrow (mtm1, Arrow (mtm2, mtm3)) ->
       let ctx = (match mtm1 with
                  | Pred (tm,_) -> (match get_head_predicate tm with
                                    | [h] -> h
                                    | _ -> raise StrengthenFailure)
                  | _ -> raise StrengthenFailure) in
       let f,g = (match mtm2 with
                  | Obj (o,_) ->
                     let g = (match (get_head_predicate o.right) with
                              | [h] -> h
                              | _ -> raise StrengthenFailure) in
                     let f = (match o.context with
                              | _::x::l -> x
                              | _ -> raise StrengthenFailure) in
                     f,g
                  | _ -> raise StrengthenFailure) in
       ctx, f, g
    | _ -> raise StrengthenFailure
  in
  let rec update_strengthen_count g_dep =
    let rec is_free_num lst =
      match lst with
      | [] -> true
      | h::t -> if (H.mem defs_table (make_ctx_name h)) then
                  false
                else
                  is_free_num t
    in
    if (is_free_num g_dep) then
      ()
    else begin
      strengthen_count := !strengthen_count + 1;
      update_strengthen_count g_dep
      end
  in
  let original_thm = sequent.goal in
  let ctx_name, f, g = extract_from_theorem original_thm in
  let ctx_clauses = (H.find defs_table ctx_name).clauses in
  let extract_term mtm =
    match mtm with
    | Pred (tm,_) ->
       (match tm with
        | App (_, [App (_, [t; _])]) -> Some t
        | _ -> None)
    | _ -> raise StrengthenFailure
  in
  let ctx_terms = List.fold_left (fun lst clause -> match (extract_term clause.head) with
                                                    | None -> lst
                                                    | Some tm -> tm::lst) []  ctx_clauses in
  let dynamic_contexts : (id, term list) H.t = H.create 10 in
  let dependencies : (id, id list) H.t = H.create 10 in
  let () = collect_contexts dynamic_contexts ctx_terms in
  let () = collect_dependencies dynamic_contexts dependencies in
  let dep_g = H.find dependencies g in
  let () = update_strengthen_count dep_g in
  let g_dep_count = List.length dep_g in
  let indep_program = independent f g dynamic_contexts dependencies in

  let g_ctx_name = make_ctx_name g in
  let ctx_subctx_name = ctx_name ^ "_subctx_" ^ g_ctx_name in
  let subctx_proof = (Induction ([1], None))::(Intros [])::(Case (Remove ("H1",[]), None))::(Search `nobounds)::
                       (List.fold_left (fun lst h -> (Apply (None, Keep ("IH",[]), [Keep ("H2",[])], [], None))::
                                                       (Search `nobounds)::lst)
                                       [] (List.tl ctx_clauses)) in
  let umtm1 = Pred (app (var Constant ctx_name 0 (tyarrow [olistty] propty))
                        [var Constant "L" 0 olistty],
                    Irrelevant) in
  let umtm2 = Pred (app (var Constant g_ctx_name 0 (tyarrow [olistty] propty))
                        [var Constant "L" 0 olistty],
                    Irrelevant) in
  let thm = Binding (Forall, [("L",olistty)], Arrow (umtm1, umtm2)) in
  let subctx_thm = TheoremProof (ctx_subctx_name, thm, subctx_proof) in
  let () = register_theorem ctx_subctx_name thm in
  let () = induction [1] in
  let () = intros [] in
  let () = case (Remove ("H1",[])) in
  let () = (try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
            | Prover.End_proof reason -> finish_proof reason) in
  let () = List.iter (fun x -> apply (Keep ("IH",[])) [Keep ("H2",[])] [];
                               try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
                               | Prover.End_proof reason -> finish_proof reason) (List.tl ctx_clauses) in

  let indep_thm_name = make_indep_name g in
  let indep_split_name = indep_thm_name ^ (if (g_dep_count > 1) then
                                             string_of_int g_dep_count
                                           else "") in
  let split_step = (if (g_dep_count > 1) then
                      let () = List.iter (fun (n, (tys,t)) -> add_lemma n tys t)
                                         (create_split_theorems indep_thm_name []) in
                      Some (SplitTheorem indep_thm_name)
                    else None) in
  let strengthening_proof = [Intros [];
                             Apply (None, Keep (ctx_subctx_name,[]),
                                    [Remove ("H1",[])], [], None);
                             Apply (None, Keep (indep_split_name,[]),
                                    [Remove ("H3",[]); Remove ("H2",[])], [], None);
                             Search `nobounds] in
  let () = sequent.goal <- original_thm in
  let () = intros [] in
  let () = apply (Keep (ctx_subctx_name,[])) [Remove ("H1",[])] [] in
  let () = apply (Keep (indep_split_name,[])) [Remove ("H3",[]); Remove ("H2",[])] [] in
  let () = try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
           | Prover.End_proof reason -> finish_proof reason in
  let strengthening_theorem = TheoremProof ("original_name", original_thm, strengthening_proof) in
  let strengthening_program = (match split_step with
                               | Some step -> [subctx_thm; step; strengthening_theorem]
                               | None -> [subctx_thm; strengthening_theorem]) in

  let program_string = program_to_string indep_program in
  let strengthening_string = program_to_string strengthening_program in
  let outfile = open_out "out.thm" in
  let () = output_string outfile program_string in
  let () = output_string outfile strengthening_string in
  let () = flush outfile in
  close_out outfile;

  strengthen_count := !strengthen_count +1;

  raise (Prover.End_proof `completed) (*let interactive prover know the proof is done*)



