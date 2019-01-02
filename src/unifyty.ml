open Term

type pos = Lexing.position * Lexing.position
let ghost : pos = (Lexing.dummy_pos, Lexing.dummy_pos)

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

type constraint_type = CFun | CArg
type constraint_info = pos * constraint_type
type constraints = (ty * ty * constraint_info) list

exception TypeInferenceFailure of ty * ty * constraint_info
exception InstGenericTyvar of string

let def_cinfo = (ghost,CArg)

let type_inference_error (pos, ct) exp act =
  Printf.printf "Typing error%s.\n%!" (position_range pos) ;
  match ct with
  | CArg ->
      Printf.eprintf "Expression has type %s but is used here with type %s\n%!"
        (ty_to_string act) (ty_to_string exp)
  | CFun ->
      Printf.eprintf "Expression is applied to too many arguments\n%!"

let occurs v ty =
  let rec aux = function
    | Ty(tys, aty) ->
       let ocr =
         match aty with
         | Tygenvar _ -> false
         | Typtr {contents=TV v'} -> v = v'
         | Tycons (_c,args) ->
            List.exists aux args
         | Typtr {contents=TT _} -> assert false
       in
       ocr || List.exists aux tys
  in aux ty

(** Unify the equality constraints between types.
    The possible results are listed as follows:
    - The unification succeeds and binds the type variables to their instances;
    - The unification fails and raises 'TypeInferenceFailure',
      meaning the some types cannot be unified no matter how the
      generic type variables are instantiated;
    - The unification may succeed or fail depending on how
      some generic variables are instantiated.
      In this case, 'InstGenericTyvar' is raised
*)
let unify_constraints ?(enable_bind=false) eqns =
  let bind_ty =
    if enable_bind then bind_ty
    else
      (fun aty ty -> match aty with
                     | Typtr t -> t := TT (observe_ty ty)
                     | _ -> assert false)
  in
  let rec aux (ty1, ty2) fail =
    let ty1 = observe_ty ty1 in
    let ty2 = observe_ty ty2 in
    match ty1, ty2 with
    | _, _ when ty1 = ty2 -> ()
    | Ty([], (Typtr {contents=TV v} as aty)), _ ->
       if occurs v ty2 then
         fail ()
       else
         bind_ty aty ty2
    | _, Ty([], (Typtr {contents=TV v} as aty)) ->
       if occurs v ty1 then
         fail ()
       else
         bind_ty aty ty1
    | Ty([], (Typtr {contents=TT _})), _
    | _, Ty([], (Typtr {contents=TT _}))
      -> assert false
    | Ty([], Tygenvar v), _
    | _, Ty([], Tygenvar v) ->
       if enable_bind then
         raise (InstGenericTyvar v)
       else
         fail ()
    | Ty([], Tycons (cty1,args1)), Ty([], Tycons (cty2,args2))
      when cty1 = cty2 && List.length args1 = List.length args2 ->
      let eqns = List.map2 (fun ty1 ty2 -> (ty1,ty2)) args1 args2
      in
      List.iter begin fun (ty1, ty2) ->
        aux (ty1, ty2) fail
      end eqns
    | Ty(ty1::tys1, bty1), Ty(ty2::tys2, bty2) ->
        aux (ty1, ty2) fail;
        aux (Ty(tys1, bty1), Ty(tys2, bty2)) fail
    | _ty1, _ty2 -> fail ()
  in

  let unify_single_constraint (ty1, ty2, p) =
    aux (ty1, ty2)
      (fun () -> raise (TypeInferenceFailure(ty1, ty2, p)))
  in

  List.iter unify_single_constraint eqns
