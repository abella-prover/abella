open Term

type pos = Lexing.position * Lexing.position
let ghost : pos = (Lexing.dummy_pos, Lexing.dummy_pos)

type expected = ty
type actual = ty
(* A constraint contains the position of the 'actual' type *)
type constraint_type = CFun | CArg
type constraint_info = pos * constraint_type
type constraints = (expected * actual * constraint_info) list
exception TypeInferenceFailure of constraint_info * expected * actual
exception InstGenericTyvar of string

let inst_gen_tyvar_msg = function v ->    
    Printf.sprintf "the generic type variable %s cannot be instantiated" v

let position_range (p1, p2) =
  let file = p1.Lexing.pos_fname in
  let line = p1.Lexing.pos_lnum in
  let char1 = p1.Lexing.pos_cnum - p1.Lexing.pos_bol in
  let char2 = p2.Lexing.pos_cnum - p1.Lexing.pos_bol in
  if file = "" then
    ""
  else
    Printf.sprintf ": file %s, line %d, characters %d-%d" file line char1 char2

let type_inference_error (pos, ct) exp act =
  Printf.printf "Typing error%s.\n%!" (position_range pos) ;
  match ct with
  | CArg ->
      Printf.eprintf "Expression has type %s but is used here with type %s\n%!"
        (ty_to_string act) (ty_to_string exp)
  | CFun ->
      Printf.eprintf "Expression is applied to too many arguments\n%!"

let rec occurs v = function
  | Ty(tys, AtmTy(cty,args)) ->
    cty = v ||
    List.exists (fun ty -> occurs v ty) tys ||
    List.exists (fun ty -> occurs v ty) args

(** Unify the equality constraints between types. 
    The possible results are listed as follows:
    - The unification succeeds and returns a list of type substitutions;
    - The unification fails and raises 'TypeInferenceFailure',
      meaning the some types cannot be unified no matter how the
      generic type variables are instantiated;
    - The unification may succeed or fail depending on how 
      some generic variables are instantiated. 
      In this case, 'InstGenericTyvar' is raised 
*)
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
    | Ty([], AtmTy(cty,args)), _ when is_tyvar cty ->
      (
        assert (args = []);
        if occurs cty ty2 then
          fail s
        else
          add_sub cty ty2 s
      )
    | _, Ty([], AtmTy(cty,args)) when is_tyvar cty ->
      (
        assert (args = []);
        if occurs cty ty1 then
          fail s
        else
          add_sub cty ty1 s
      )
    | Ty([], AtmTy(cty,args)), _ when is_gen_tyvar cty ->
      (
        assert (args = []);
         raise (InstGenericTyvar cty)
      )
    | _, Ty([], AtmTy(cty,args)) when is_gen_tyvar cty ->
      (
        assert (args = []);
        raise (InstGenericTyvar cty)
      )
    | Ty([], AtmTy(cty1,args1)), Ty([], AtmTy(cty2,args2)) 
      when cty1 = cty2 && List.length args1 = List.length args2 ->
      let eqns = List.map2 (fun ty1 ty2 -> (ty1,ty2)) args1 args2 
      in
      List.fold_left begin fun s (ty1, ty2) ->
        aux s (ty1, ty2) fail
      end s eqns
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

(* Similar to unify_constraints, but returns 
   the type substituions in an option type *)
let solve_constraints eqns : (id * ty) list option =
  try
    Some (unify_constraints eqns)
  with
  | TypeInferenceFailure _ -> None
  | InstGenericTyvar v -> failwith (inst_gen_tyvar_msg v)
  

let ty_compatible ty1 ty2 =
  try
    let _ = unify_constraints [(ty1, ty2, (ghost,CArg))] in
    true
  with
  | TypeInferenceFailure _
  | InstGenericTyvar _ ->
    false
