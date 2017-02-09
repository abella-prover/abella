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
       var Eigen id 0 ty (*Eigen and 0 placeholders for now*)
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
  let rec get_name i =
    let name = base ^ (string_of_int i) in
    if (fresh_in_term tm name) then
      name
    else
      get_name (i + 1)
  in
  if (fresh_in_term tm base) then
    base
  else
    get_name 0

let fresh_name_term_lst tmlst base =
  let fresh_in_lst lst name =
    List.fold_left (fun bool t -> bool && (fresh_in_term t name)) true lst
  in
  let rec get_name i =
    let name = base ^ (string_of_int i) in
    if (fresh_in_lst tmlst name) then
      name
    else
      get_name (i + 1)
  in
  if (fresh_in_lst tmlst base) then
    base
  else
    get_name 0

let fresh_name_metaterm mtm base =
  let rec fresh mtm var =
    match mtm with
    | True -> true
    | False -> true
    | Eq (t1,t2) -> (fresh_in_term t1 var) && (fresh_in_term t2 var)
    | Obj (o,r) ->(fresh_in_term o.right var) && (List.fold_left (fun bool t -> bool && (fresh_in_term t var)) true o.context)
    | Arrow (mtm1,mtm2) -> (fresh mtm1 var) && (fresh mtm2 var)
    | Binding (b,idtylst,mtm') -> (fresh mtm' var) && (fresh_in_tyctx idtylst var)
    | Or (mtm1,mtm2) -> (fresh mtm1 var) && (fresh mtm2 var)
    | And (mtm1,mtm2) -> (fresh mtm1 var) && (fresh mtm2 var)
    | Pred (tm,r) -> fresh_in_term tm var
  in
  let rec get_name i =
    if (fresh mtm (base ^ (string_of_int i))) then
      base ^ (string_of_int i)
    else
      get_name (i + 1)
  in
  if (fresh mtm base) then
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
  let fresh_in_lst lst name =
    List.fold_left (fun bool ut -> bool && (fresh_in_uterm ut name)) true lst
  in
  let rec get_name i =
    let name = base ^ (string_of_int i) in
    if (fresh_in_lst utmlst name) then
      name
    else
      get_name (i + 1)
  in
  if (fresh_in_lst utmlst base) then
    base
  else
    get_name 0

let fresh_name_uterm ut base =
  let rec get_name i =
    let name = base ^ (string_of_int i) in
    if (fresh_in_uterm ut name) then
      name
    else
      get_name (i + 1)
  in
  if (fresh_in_uterm ut base) then
    base
  else
    get_name 0

let fresh_name_umetaterm umtm base =
  let rec fresh umtm var =
    match umtm with
    | UTrue -> true
    | UFalse -> true
    | UEq (ut1,ut2) -> (fresh_in_uterm ut1 var) && (fresh_in_uterm ut2 var)
    | UAsyncObj (ut1,ut2,r) -> (fresh_in_uterm ut1 var) && (fresh_in_uterm ut2 var)
    | USyncObj (ut1,ut2,ut3,r) -> (fresh_in_uterm ut1 var) && (fresh_in_uterm ut2 var) && (fresh_in_uterm ut3 var)
    | UArrow (umtm1,umtm2) -> (fresh umtm1 var) && (fresh umtm2 var)
    | UBinding (b,idtylst,umtm') -> (fresh_in_tyctx idtylst var) && (fresh umtm' var)
    | UOr (umtm1,umtm2) -> (fresh umtm1 var) && (fresh umtm2 var)
    | UAnd (umtm1,umtm2) -> (fresh umtm1 var) && (fresh umtm2 var)
    | UPred (ut,r) -> fresh_in_uterm ut var
  in
  let rec get_name i =
    if (fresh umtm (base ^ (string_of_int i))) then
      base ^ (string_of_int i)
    else
      get_name (i + 1)
  in
  if (fresh umtm base) then
    base
  else
    get_name 0

type set_ref =
  | Ref of id
  | Formula of term

let pred_list : string list ref = ref []
let pred_arities : (id, int) H.t = H.create 10

let dynamic_contexts : (id, term list) H.t = H.create 10

let dependencies : (id, id list) H.t = H.create 10

exception StrengthenFailure


let collect_contexts () =
  let ctx_col : (string, set_ref list) H.t = H.create 10 in
  let gamma' = ref !clauses in

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
    List.iter (fun h -> H.add output h [];
                        if (not (H.mem cnstrnts h)) then (*add empty context constraints*)
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

  (*assumes a predicate is defined for each as in http://abella-prover.org/independence/code/stlc.html for ty and tm*)
  let extract_all_predicates () =
    let rec collect_preds lst =
      match lst with
      | [] -> []
      | (pred,Poly (_,ty))::tl -> 
         if (ty = oty) then
           let () = H.add pred_arities pred 0 in
           pred::(collect_preds tl)
         else
           match ty with
           (*match higher-order types*)
           | Ty ([Ty ([x],_)],_) -> collect_preds tl
           (*match type prediates*)
           | Ty ([x],bty) ->
              if ((tybase bty) = oty) then
                let () = H.add pred_arities pred 1 in
                pred::(collect_preds tl)
              else
                collect_preds tl
           | _ -> collect_preds tl
    in
    let _,l = !sign in
    collect_preds l
            
  in
  pred_list := extract_all_predicates ();
  simplify_constraints ctx_col dynamic_contexts
  (*display all predicates in pred_list -- testing purposes only*)
  (*;print_string "Predicates\n";
  List.iter (fun p -> print_string (p ^ "; ")) !pred_list;
  print_string "\n"*)
  (*display dynamic contexts --  testing purposes only*)
  (*;print_string "Dynamic Contexts\n";
  H.iter (fun p l -> print_string ("Pred: " ^ p ^ "\n");
                     List.iter (fun t -> print_string ((term_to_string t) ^ ";\n")) l
         ) dynamic_contexts*)
  (*display sign*)
  (*;let x,y = !sign in
   let _ = List.iter (fun (s,p) -> match p with
                                   | Poly (_,t) -> print_string (s^" : "^(ty_to_string t)^"\n")) y in
   let _ = print_string "\n" in
   List.iter (fun s -> print_string (s ^ "\n")) x*)


let collect_dependencies () =
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
  (*display dependencies --  testing purposes only*)
  (*;print_string "Dependencies\n";
  H.iter (fun p l -> print_string ("Pred: " ^ p ^ "\n");
                     List.iter (fun t -> print_string (t ^ "; ")) l; print_string "\n";
         ) dependencies*)
                       
                       
(*Prove g independent of f*)
let independent f g =
  
  let outfile = open_out "out.thm" in
  
  let make_ctx_name pred =
    "ctx_" ^ pred
               
  in
  let make_subctx_name pred_sub pred_super =
    (make_ctx_name pred_sub) ^ "_subctx_" ^ (make_ctx_name pred_super)
                                              
  in
  let rec make_variables_universal trm =
    match (observe trm) with
    | Var v -> if (v.tag = Constant) then
                 trm
               else
                 var v.tag (String.uppercase v.name) v.ts v.ty
    | App (t, tlist) -> app (make_variables_universal t) (List.map make_variables_universal tlist)
    | _ -> trm
             
  in
  let rec collect_quantified_variables trm =
    match (observe trm) with
    | Var v -> if (v.tag = Constant) then
                 []
               else
                 [(v.name,v.ty)]
    | App (t, tlist) ->
       (collect_quantified_variables t) @ (List.fold_right (fun tm lst -> (collect_quantified_variables tm) @ lst) tlist [])
    | _ -> []
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
  let register_theorem name thm =
    add_lemma name [] thm;
    theorem thm
            
  in
  let finish_proof reason =
    match reason with
    | `completed -> reset_prover ()
    | _ -> failwith "Automated proof not completed"
                    
  in
  let define_ctx pred =
    let ctx_formulas = H.find dynamic_contexts pred in
    let ctx_name = make_ctx_name pred in
    let rec add_formula form_lst def_str =
      match form_lst with
      | [] -> (def_str ^ ".\n\n", [])
      | h::t -> 
         let cap_term = make_variables_universal h in
         let ctx_var = fresh_name_term cap_term "L" in
         let new_def = def_str ^ ";\n  " ^ ctx_name ^ " ((" ^ (term_to_string cap_term) ^ ") :: " ^ ctx_var ^ ") := " ^
                         ctx_name ^ " " ^ ctx_var in
         let s,l = add_formula t new_def in
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
         (s, (def,def_proof)::l)
    in
    let rec build_mem_thm form_lst mem_var thm_str =
      match form_lst with
      | [] -> (thm_str, False)
      | [h] ->
         let quant_vars = collect_quantified_variables h in
         let quantifications = List.fold_right (fun (name,ty) s -> s ^ "exists " ^ name ^ ", ") quant_vars "" in
         let mtm_quantifications = (if ((List.length quant_vars) > 0) then
                                      Binding (Exists,
                                               List.fold_right (fun x l -> x::l) quant_vars [],
                                               Eq (var Logic mem_var 0 oty, h))
                                    else
                                      Eq (var Logic mem_var 0 oty, h)
                                   ) in
         let new_thm = thm_str ^ quantifications ^ mem_var ^ " = (" ^ (term_to_string h) ^ ").\n" in
         let full_thm,_ = build_mem_thm [] mem_var new_thm in
         (full_thm, mtm_quantifications)
      | h::t ->
         let quant_vars = collect_quantified_variables h in
         let quantifications = List.fold_right (fun (name,ty) s -> s ^ "exists " ^ name ^ ", ") quant_vars "" in
         let mtm_quantifications = Binding (Exists,
                                            List.fold_right (fun x l -> x::l) quant_vars [],
                                            Eq (var Logic mem_var 0 oty, h)) in
         let new_thm = thm_str ^ quantifications ^ mem_var ^ " = (" ^ (term_to_string h) ^ ") \\/ " in
         let full_thm,mtm = build_mem_thm t mem_var new_thm in
         (full_thm, Or (mtm_quantifications, mtm))
    in
    let rec add_proof_step form_lst prf_str =
      match form_lst with
      | [] -> prf_str
      | h::t ->
         let () = case (Remove ("H2", [])) in
         let () = search ~witness:WMagic ~handle_witness:(fun x -> ()) () in
         let () = apply (Keep ("IH",[])) [(Keep ("H3",[])); (Keep ("H4",[]))] [] in
         let () = (
             try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
             | Prover.End_proof reason -> finish_proof reason
           ) in
         let new_prf = prf_str ^ "\n  case H2. search. apply IH to H3 H4. search." in
         add_proof_step t new_prf
    in
    let rec add_grown_context_lemma form_lst prf_str index =
      match form_lst with
      | [] -> prf_str ^ "\n"
      | h::t ->
         let thm_name = ctx_name ^ "_plus" ^ (string_of_int index) in
         let thm1 = Pred (app (var Constant ctx_name 0 (tyarrow [olistty] propty))
                              [var Logic "L" 0 olistty],
                          Irrelevant) in
         let thm2 = Pred (app (var Constant ctx_name 0 (tyarrow [olistty] propty))
                              [app (var Constant "::" 0 (tyarrow [oty; olistty] olistty))
                                   [h; var Logic "L" 0 olistty]],
                          Irrelevant) in
         let thm = Binding (Forall, [("L",olistty)], Arrow (thm1, thm2)) in
         let () = register_theorem thm_name thm in
         let () = (
             try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
             | Prover.End_proof reason -> finish_proof reason
           ) in
         let new_str = "Theorem " ^ thm_name ^ " : " ^ (metaterm_to_string thm) ^ ". search.\n" in
         add_grown_context_lemma t (prf_str ^ new_str) (index + 1)
    in

    let ctx_type = tyarrow [olistty] propty in
    let def_start = "Define " ^ ctx_name ^" : olist -> prop by\n  " ^ ctx_name ^ " nil" in
    let definition,defs = add_formula ctx_formulas def_start in
    let full_defs = (UPred (UApp ((Lexing.dummy_pos,Lexing.dummy_pos),
                                  UCon ((Lexing.dummy_pos,Lexing.dummy_pos),
                                        ctx_name, (tyarrow [olistty] propty)),
                                  UCon ((Lexing.dummy_pos,Lexing.dummy_pos),
                                        "nil", olistty)), Irrelevant),
                     UTrue)::defs in
    let def = Define (Inductive, [(ctx_name,ctx_type)], full_defs) in
    let _ = register_definition def in
    output_string outfile definition;

    let growing_ctx_lemmas = add_grown_context_lemma ctx_formulas "" 1 in
    output_string outfile growing_ctx_lemmas;

    let ctx_var = fresh_name_term_lst ctx_formulas "L" in
    let mem_var = fresh_name_term_lst ctx_formulas "E" in
    let thm_stmt = "Theorem " ^ ctx_name ^ "_mem : forall " ^ ctx_var ^ " " ^ mem_var ^ ", " ^
                     ctx_name ^ " L -> member E L -> " in
    let full_thm_str,mtm = build_mem_thm ctx_formulas mem_var thm_stmt in
    let thm_1 = Pred (app (var Constant ctx_name 0 (tyarrow [olistty] propty))
                          [var Logic ctx_var 0 olistty],
                      Irrelevant) in
    let thm_2 = Pred (app (var Constant "member" 0 (tyarrow [oty; olistty] propty))
                          [var Logic mem_var 0 oty; var Logic ctx_var 0 olistty],
                      Irrelevant) in
    if (List.length ctx_formulas > 0) then
      let thm = Binding (Forall, [(ctx_var,olistty); (mem_var,oty)], Arrow (thm_1, Arrow (thm_2, mtm))) in
      let _ = register_theorem (ctx_name ^ "_mem") thm in
      let prf_start = "induction on 1. intros. case H1.\n  case H2." in
      let () = induction [1] in
      let () = intros [] in
      let () = case (Remove ("H1", [])) in
      let () = case (Keep ("H2", [])) in
      let prf = add_proof_step ctx_formulas prf_start in
      let thm_prf_complete = full_thm_str ^ prf ^ "\n\n" in
      let () = output_string outfile thm_prf_complete in
      flush outfile
    else
      let full_thm_str = thm_stmt ^ "false.\n" in
      let thm = Binding (Forall, [(ctx_var,olistty); (mem_var,oty)], Arrow (thm_1, Arrow (thm_2, False))) in
      let _ = register_theorem (ctx_name ^ "_mem") thm in
      let prf = "induction on 1. intros. case H1.\n  case H2." in
      let () = induction [1] in
      let () = intros [] in
      let () = case (Remove ("H1", [])) in
      let () = (try case (Keep ("H2", [])) with
                | Prover.End_proof reason -> finish_proof reason
               ) in
      let thm_prf_complete = full_thm_str ^ prf ^ "\n\n" in
      let () = output_string outfile thm_prf_complete in
      flush outfile

  in
  let subctx_thm subp pred subp_ctx =
    let rec add_step lst prf_str =
      match lst with
      | [] -> prf_str ^ "\n\n"
      | h::t ->
         let () = apply (Keep ("IH",[])) [(Keep ("H2",[]))] [] in
         let () = (
             try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
             | Prover.End_proof reason -> finish_proof reason
           ) in
         let new_prf = prf_str ^ "\n  apply IH to H2. search." in
         add_step t new_prf
    in
    let subctx_name = make_subctx_name subp pred in
    let subp_ctx_name = make_ctx_name subp in
    let pred_ctx_name = make_ctx_name pred in
    let thm_prf = "Theorem " ^ subctx_name ^ " : forall L, " ^ subp_ctx_name ^
                    " L -> " ^ pred_ctx_name ^ " L.\ninduction on 1. intros. case H1.\n  search." in
    let umtm1 = Pred (app (var Constant subp_ctx_name 0 (tyarrow [olistty] propty))
                          [var Logic "L" 0 olistty],
                      Irrelevant) in
    let umtm2 = Pred (app (var Constant pred_ctx_name 0 (tyarrow [olistty] propty))
                          [var Logic "L" 0 olistty],
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
    let subctx_prf = add_step subp_ctx thm_prf in
    let () = output_string outfile subctx_prf in
    flush outfile
          
  in
  let indep_theorem g_dep =
    let rec build_theorem dep_lst thm =
      match dep_lst with
      | [] -> failwith "Found empty dependency list"
      | [h] ->
         let ctx_name = make_ctx_name h in
         let ctx_var = "L" in
         let f_str = List.fold_left (fun str tm -> str ^ ", " ^ (term_to_string tm)) "" f in
         let start_part = "\n  (forall " ^ ctx_var ^ ", " ^ ctx_name ^ " " ^ ctx_var ^
                            " -> {" ^ ctx_var ^ f_str ^ " |- " ^ h ^ "}" in
         let end_part = " -> {" ^ ctx_var ^ " |- " ^ h  ^ "})" in
         let full_thm_str = thm ^ start_part ^ end_part ^ ".\n" in
         let umtm1 = Pred (app (var Constant ctx_name 0 (tyarrow [olistty] propty))
                               [var Logic ctx_var 0 olistty],
                           Irrelevant) in
         let umtm2 = Obj ({context = [List.fold_left (fun old tm -> app (var Constant "::" 0 (tyarrow [oty; olistty] olistty))
                                                                        [tm; old]) (var Logic ctx_var 0 olistty) f];
                           right = var Constant h 0 oty;
                           mode = Async;}, Irrelevant) in
         let umtm3 = Obj ({context = [var Logic ctx_var 0 olistty];
                           right = var Constant h 0 oty;
                           mode = Async;}, Irrelevant) in
         let this_dep = Binding (Forall, [(ctx_var,olistty)], Arrow (umtm1, Arrow (umtm2, umtm3))) in
         (full_thm_str, this_dep)
      | h::t ->
         let ctx_name = make_ctx_name h in
         let ctx_var = "L" in
         let f_str = List.fold_left (fun str tm -> str ^ ", " ^ (term_to_string tm)) "" f in
         let start_part = "\n  (forall " ^ ctx_var ^ ", " ^ ctx_name ^ " " ^ ctx_var ^
                            " -> {" ^ ctx_var ^  f_str ^ " |- " ^ h ^ "}" in
         let end_part = " -> {" ^ ctx_var ^ " |- " ^ h  ^ "}) /\\" in
         let full_thm_str,rest_of_thm = build_theorem t (thm ^ start_part ^ end_part) in
         let umtm1 = Pred (app (var Constant ctx_name 0 (tyarrow [olistty] propty))
                               [var Logic ctx_var 0 olistty],
                           Irrelevant) in
         let umtm2 = Obj ({context = [List.fold_left (fun old tm -> app (var Constant "::" 0 (tyarrow [oty; olistty] olistty))
                                                                        [tm; old]) (var Logic ctx_var 0 olistty) f];
                           right = var Constant h 0 oty;
                           mode = Async;}, Irrelevant) in
         let umtm3 = Obj ({context = [var Logic ctx_var 0 olistty];
                           right = var Constant h 0 oty;
                           mode = Async;}, Irrelevant) in
         let this_dep = Binding (Forall, [(ctx_var,olistty)], Arrow (umtm1, Arrow (umtm2, umtm3))) in
         (full_thm_str, And (this_dep, rest_of_thm))
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
      let rec get_antecedents trm =
        let ob_tm = observe trm in
        match ob_tm with
        | Var  v -> []
        | App  (t,tlst) -> if (is_imp ob_tm) then
                             let a,b = extract_imp ob_tm in
                             let lst = get_antecedents b in
                             a::lst
                           else
                             [ob_tm]
        | _ -> failwith "Term should not contain anything but Var and App"
      in
      let iterate_antecedents pred lst index =
        let apply_ind_hyp tm hyp_ind =
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
          let rec iter_grown_ctx lst head index =
            match lst with
            | [] -> ("",index)
            | h::t ->
               let ctx_plus_name = find_gc_lemma h head in
               let hyp_name = "H" ^ (string_of_int index) in
               let () = apply (Keep (ctx_plus_name,[])) [Keep (hyp_name,[])] [] in
               let prf_str = "        apply " ^ ctx_plus_name ^ " to " ^ hyp_name ^ ".\n" in
               let rest_of_prf, max_index = iter_grown_ctx t head (index + 1) in
               prf_str ^ rest_of_prf, max_index
          in
          let head = List.hd (get_head_predicate tm) in
          let subctx_lemma = make_subctx_name pred head in
          let () = apply (Keep (subctx_lemma,[])) [Keep ("H1",[])] [] in
          let subctx_application = "      apply " ^ subctx_lemma ^ " to H1.\n" in
          let grown_ctx = get_antecedents tm in
          let prf_str, last_ctx_ind = iter_grown_ctx grown_ctx head (hyp_ind + 1) in
          let ih = find_ih g_dep head in
          let ctx_hyp = "H" ^ (string_of_int last_ctx_ind) in
          let pred_hyp = "H" ^ (string_of_int index) in
          let () = apply (Keep (ih, [])) [Keep (ctx_hyp, []); Keep (pred_hyp, [])] [] in
          let final_prf = "      apply " ^ ih ^ " to " ^ ctx_hyp ^ " " ^ pred_hyp ^ ".\n" in
          subctx_application ^ prf_str ^ final_prf
        in

        let rec aux lst index =
          match lst with
          | [] -> ""
          | h::t ->
             let prf = apply_ind_hyp h index in
             let rest_of_prf = aux t (index + 1) in
             prf ^ rest_of_prf
        in aux lst index
               
      in
      let rec build_reg_ctx_prf pred lst prf =
        match lst with
        | [] -> prf
        | h::t ->
           if ((get_head_predicate h) = [pred]) then
             let antecedents = get_antecedents h in
             let new_prf_step = (iterate_antecedents pred antecedents 3) ^
                                  "      search.\n" in
             let () = search ~witness:WMagic ~handle_witness:(fun x -> ()) () in
             build_reg_ctx_prf pred t new_prf_step
           else
             build_reg_ctx_prf pred t ""
      in
      let build_dyn_ctx_prf pred =
        let rec iterate_ctx pred obj_hyp_index lst prf =
          match lst with
          | [] -> prf
          | h::t ->
             let new_prf_step = "      case H3.\n" in
             let () = (try case (Remove ("H3", [])) with
                       | Prover.End_proof reason -> finish_proof reason
                      ) in
             if ((get_head_predicate h) = [pred]) then
               let antecedents = get_antecedents h in
               let new_prf_step = new_prf_step ^ (iterate_antecedents pred antecedents obj_hyp_index) ^
                                    "        search.\n" in
               let () = (try search ~witness:WMagic ~handle_witness:(fun x -> ()) () with
                         | Prover.End_proof reason -> finish_proof reason
                        ) in
               iterate_ctx pred obj_hyp_index t (prf ^ new_prf_step)
             else
               iterate_ctx pred obj_hyp_index t (prf ^ new_prf_step)
        in
        let rec iter_indep lst index =
          match lst with
          | [] -> ""
          | h::t ->
             let mem_hyp = "H" ^ (string_of_int index) in
             let () = case (Remove (mem_hyp, [])) in
             let () = case (Remove ("H3", [])) in
             "    case " ^ mem_hyp ^ ". case H3.\n" ^ (iter_indep t (index + 1))
        in
        let prf_start = iter_indep f 4 in
        let ctx_mem_name = (make_ctx_name pred) ^ "_mem" in
        let () = (try apply (Keep (ctx_mem_name,[])) [(Keep ("H1",[])); (Keep ("_",[]))] [] with
                  | Prover.End_proof reason ->
                     finish_proof reason
                 )in
        let prf_start = prf_start ^ "    apply " ^ ctx_mem_name ^ " to H1 _.\n" in
        let ctx_formulas = H.find dynamic_contexts pred in
        let f_len = List.length f in
        let prf_start,obj_hyp_index = (if ((List.length ctx_formulas) > 1) then
                                         let mem_eq_hyp = "H" ^ (string_of_int (5 + f_len)) in
                                         let () = case (Remove (mem_eq_hyp,[])) in
                                         prf_start ^ "      case " ^ mem_eq_hyp ^ ".\n", (5 + f_len + 1)
                                       else
                                         prf_start, (5 + f_len)) in
        let dyn_ctx_prf_str = iterate_ctx pred obj_hyp_index ctx_formulas prf_start in
        dyn_ctx_prf_str
      in
      let rec each_pred lst prf =
        match lst with
        | [] -> prf
        | h::t ->
           let () = intros [] in
           let () = case  (Remove ("H2", [])) in
           let start = "  intros. case H2.\n" in
           let reg_ctx_prf = build_reg_ctx_prf h !clauses "" in
           let dyn_ctx_prf = build_dyn_ctx_prf h in
           let new_prf = prf ^ start ^ reg_ctx_prf ^ dyn_ctx_prf ^ "\n" in
           each_pred t new_prf
      in
      let prf = (List.fold_right (fun x s -> s ^ " 2") g_dep "induction on") ^ "." in
      let () = induction (List.map (fun x -> 2) g_dep) in
      if ((List.length g_dep) > 1) then
        let () = split false in
        let prf = prf ^ " split.\n" in
        each_pred g_dep prf
      else
        let prf = prf ^ "\n" in
        each_pred g_dep prf
    in
    let thm_start = "Theorem " ^ g ^ "_indep" ^ " : " in
    let theorem_str,mtm = build_theorem g_dep thm_start in
    let () = register_theorem (g ^ "_indep") mtm in
    let () = output_string outfile theorem_str in
    let proof = build_proof g_dep in
    let () = output_string outfile proof in
    flush outfile

  in
  let dep_g = H.find dependencies g in
  (*if (List.mem f dep_g) then
    failwith ("Cannot prove " ^ g ^ " independent of " ^ f ^ "--dependency exists");*)
  List.iter define_ctx dep_g;
  List.iter (fun x -> let x_ctx = H.find dynamic_contexts x in
                      let dep_x = H.find dependencies x in
                      List.iter (fun dep_pred -> subctx_thm x dep_pred x_ctx) dep_x) dep_g;
  (*try indep_theorem dep_g with
  | _ -> raise StrengthenFailure;*)
  indep_theorem dep_g;
  close_out outfile
