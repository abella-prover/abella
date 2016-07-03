open Term

type pos = Lexing.position * Lexing.position

type expected = ty
type actual = ty
(* A constraint contains the position of the 'actual' type *)
type constraint_type = CFun | CArg
type constraint_info = pos * constraint_type
type constraints = (expected * actual * constraint_info) list
exception TypeInferenceFailure of constraint_info * expected * actual
type error_info = InstGenericTyvar of string
exception TypeInferenceError of error_info

let type_inference_error (pos, ct) exp act =
  Printf.fprintf !Printf.out "Typing error%s.\n%!" (position_range pos) ;
  match ct with
  | CArg ->
      eprintf "Expression has type %s but is used here with type %s\n%!"
        (ty_to_string act) (ty_to_string exp)
  | CFun ->
      eprintf "Expression is applied to too many arguments\n%!"

let rec occurs v = function
  | Ty(tys, AtmTy(cty,args)) ->
    cty = v ||
    List.exists (fun ty -> occurs v ty) tys ||
    List.exists (fun ty -> occurs v ty) args

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
         raise (TypeInferenceError (InstGenericTyvar cty))
      )
    | _, Ty([], AtmTy(cty,args)) when is_gen_tyvar cty ->
      (
        assert (args = []);
        raise (TypeInferenceError (InstGenericTyvar cty))
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
