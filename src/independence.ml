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

type set_ref =
  | Ref of id
  | Formula of term

let pred_list : string list ref = ref []

let dynamic_contexts : (id, term list) H.t = H.create 10

let dependencies : (id, id list) H.t = H.create 10


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
           pred::(collect_preds tl)
         else
           match ty with
           (*match higher-order types*)
           | Ty ([Ty ([x],_)],_) -> collect_preds tl
           (*match type prediates*)
           | Ty ([x],bty) ->
              if ((tybase bty) = oty) then
                pred::(collect_preds tl)
              else
                collect_preds tl
           | _ -> collect_preds tl
    in
    let _,l = !sign in
    collect_preds l

  in pred_list := extract_all_predicates ();
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
         let changed = List.fold_right (fun p changed -> if (not (List.mem p (H.find output pred))) then
                                                           let _ = H.replace output pred (p::(H.find output pred)) in
                                                           true
                                                         else
                                                           changed) (H.find output dep_pred) false in
         (add_dependencies tail pred) || changed

    in
    let rec simplify_aux () =
      let a = List.fold_right (fun h changed -> add_dependencies (H.find cnstrnts h) h) !pred_list false in
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
                   [v.name]
      | App (t, tlist) ->
         (collect_quantified_variables t) @ (List.fold_right (fun tm lst -> (collect_quantified_variables tm) @ lst) tlist [])
      | _ -> []
  in

  let rec term_to_uterm trm =
    match (observe trm) with
    | Var v -> UCon ((Lexing.dummy_pos,Lexing.dummy_pos), v.name, v.ty) (*dummy type for now*) 
    | App (tm1,[tm2]) -> UApp ((Lexing.dummy_pos,Lexing.dummy_pos), term_to_uterm tm1, term_to_uterm tm2)
    | _ -> bugf "Should not have any terms but Vars and Apps"

  in
  let define_ctx pred =
    let ctx_formulas = H.find dynamic_contexts pred in
    let ctx_name = make_ctx_name pred in
    let rec add_formula form_lst def_str =
      match form_lst with
      | [] -> (def_str ^ ".\n\n",
               [(UPred (UApp ((Lexing.dummy_pos,Lexing.dummy_pos),
                              UCon ((Lexing.dummy_pos,Lexing.dummy_pos), ctx_name, tyarrow [olistty] propty),
                              UCon ((Lexing.dummy_pos,Lexing.dummy_pos), "nil", olistty)), Irrelevant),
               UTrue)])
      | h::t -> (*TODO--do checking/replacing to remove names L, E*)
         let cap_term = make_variables_universal h in
         let new_def = def_str ^ ";\n\t" ^ ctx_name ^ " ((" ^ (term_to_string cap_term) ^ ") :: L) := " ^ ctx_name ^ " L" in
         let s,l = add_formula t new_def in
         let utrm = term_to_uterm cap_term in
         let udef = UPred (UApp ((Lexing.dummy_pos,Lexing.dummy_pos),
                                 UCon ((Lexing.dummy_pos,Lexing.dummy_pos), ctx_name, tyarrow [olistty] propty),
                                 (UApp ((Lexing.dummy_pos,Lexing.dummy_pos),
                                        UApp ((Lexing.dummy_pos,Lexing.dummy_pos),
                                              UCon ((Lexing.dummy_pos,Lexing.dummy_pos), "::", tyarrow [oty; olistty] olistty),
                                              utrm),
                                        UCon ((Lexing.dummy_pos,Lexing.dummy_pos), "L", olistty)))), Irrelevant) in
         let udef_proof = UPred (UApp ((Lexing.dummy_pos,Lexing.dummy_pos),
                                       UCon ((Lexing.dummy_pos,Lexing.dummy_pos), ctx_name, tyarrow [olistty] propty),
                                       UCon ((Lexing.dummy_pos,Lexing.dummy_pos), "L", olistty)),
                                 Irrelevant) in
         (s, (udef,udef_proof)::l)
    in
    let rec add_proof_step form_lst thm_str prf_str =
      match form_lst with
      | [] -> thm_str ^ prf_str ^ "\n\n"
      | [h] ->
         let quant_vars = collect_quantified_variables h in
         let quantifications = List.fold_right (fun x s -> s ^ "exists " ^ x ^ ", ") quant_vars "" in
         let new_thm = thm_str ^ quantifications ^ "E = (" ^ (term_to_string h) ^ ").\n" in
         let new_prf = prf_str ^ "\n\tcase H2. search. apply IH to H3 H4. search." in
         add_proof_step [] new_thm new_prf
      | h::t -> (*TODO--capitalizing variable names, adding exists for variables*)
         let quant_vars = collect_quantified_variables h in
         let quantifications = List.fold_right (fun x s -> s ^ "exists " ^ x ^ ", ") quant_vars "" in
         let new_thm = thm_str ^ quantifications ^ "E = (" ^ (term_to_string h) ^ ") \\/" in
           let new_prf = prf_str ^ "\n\tcase H2. search. apply IH to H3 H4. search." in
         add_proof_step t new_thm new_prf
    in

    let ctx_type = tyarrow [olistty] propty in
    let def_start = "Define " ^ ctx_name ^" : olist -> prop by\n\t" ^ ctx_name ^ " nil" in
    let definition,udefs = add_formula ctx_formulas def_start in
    let def = Define (Inductive, [(ctx_name,ctx_type)], udefs) in
    let _ = register_definition def in
    output_string outfile definition;

    if (List.length ctx_formulas > 0) then
      let thm_stmt = "Theorem " ^ ctx_name ^ "_mem : forall L E, " ^ ctx_name ^ " L -> member E L -> " in
      let prf_start = "induction on 1. intros. case H1.\n\tcase H2." in
      let thm_prf = add_proof_step ctx_formulas thm_stmt prf_start in
      let () = output_string outfile thm_prf in
      flush outfile

  in
  let subctx_thm pred g_ctx =
    let rec add_step lst prf_str =
      match lst with
      | [] -> prf_str ^ "\n\n"
      | h::t ->
         let new_prf = prf_str ^ "\n\tapply IH to H2. search." in
         add_step t new_prf
    in
    let thm_prf = "Theorem " ^ (make_subctx_name g pred) ^ " : forall L, ctx_" ^
                    g ^ " L -> ctx_" ^ pred ^ " L.\ninduction on 1. intros. case H1.\n\tsearch." in
    let subctx_prf = add_step g_ctx thm_prf in
    let () = output_string outfile subctx_prf in
    flush outfile

  in
  let indep_theorem g_dep =
    let rec build_theorem dep_lst thm =
      match dep_lst with
      | [] -> thm ^ ".\n"
      | [h] ->
         let start_part = "\n\t(forall L, " ^ (make_ctx_name h) ^ " L -> {L, " ^ f ^ " |- " ^ g ^ "}" in
         let end_part = "-> {L |- " ^ g  ^ "})" in
         build_theorem [] (thm ^ start_part ^ end_part)
      | h::t ->
         let start_part = "\n\t(forall L, " ^ (make_ctx_name h) ^ " L -> {L, " ^ f ^ " |- " ^ g ^ "}" in
         let end_part = "-> {L |- " ^ g  ^ "}) /\\" in
         build_theorem t (thm ^ start_part ^ end_part)
    in
    let build_proof g_dep =
      let rec build_reg_ctx_prf pred lst prf =
        match lst with
        | [] -> prf
        | h::t -> build_reg_ctx_prf pred t prf
      in
      let rec each_pred lst prf =
        match lst with
        | [] -> prf
        | h::t ->
           let start = "\tintros. case H2.\n" in
           let reg_ctx_prf = build_reg_ctx_prf h !clauses "" in
           let new_prf = prf ^ start ^ reg_ctx_prf in
           each_pred t new_prf
      in
      let prf = (List.fold_right (fun x s -> s ^ " 2") g_dep "induction on") ^ ". split.\n" in
      each_pred g_dep prf
    in
    let theorem = build_theorem g_dep ("Theorem " ^ g ^ "_indep_" ^ f ^ " : ") in
    let () = output_string outfile theorem in
    let proof = build_proof g_dep in
    let () = output_string outfile proof in
    flush outfile

  in
  let dep_g = H.find dependencies g in
  if (List.mem f dep_g) then
    failwith ("Cannot prove " ^ g ^ " independent of " ^ f ^ "--dependency exists");
  List.iter define_ctx dep_g;
  let g_ctx = H.find dynamic_contexts g in
  List.iter (fun dep_pred -> subctx_thm dep_pred g_ctx) dep_g;
  indep_theorem dep_g;
  close_out outfile
