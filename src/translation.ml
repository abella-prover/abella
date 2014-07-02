open Term
open Uterm
(* open Typing *)

exception TranslationError of string

let is_type t = app (const "lfisty" (tyarrow [lftypety] oty)) [t]

let has_type term ty pos =
  app (const "lfhas" (tyarrow [lfobjty; lftypety] oty)) [term; ty]

let rec trans_type t =
  match t with
  | UCon(p, x, ty) -> lfobjty
  | UType(p) -> lftypety
  | UImp(p, t1, t2) -> tyarrow [trans_type t1] (trans_type t2)
  | UPi(p, x, a, b) -> tyarrow [trans_type a] (trans_type b)
  | UApp(p, t1, t2) -> trans_type t1
  | _ -> raise (TranslationError "invalid type")

let rec trans_term t =
  match t with
  | UCon(p, x, ty) -> const x ty
  | UApp(p, t1, t2) -> app (trans_term t1) [(trans_term t2)]
  | UAbs(p, x, a, b) -> abstract x (trans_type a) (trans_term b)
  | _ -> raise (TranslationError "invalid term")

let lfproof_var = "lfx"
let defaultused : (id * term) list =
  [lfproof_var, Term.var Constant lfproof_var 0 lfobjty]

let rec translate ?(used=defaultused) t =
  match t with
  | UJudge(p, UAbs(q, x, a, b), UPi(q', x', a', b')) ->
    if x=x' && a= a' then (* MKS: shouldn't this be alpha equiv rather than eq? *)
      translate_abstraction_type ~used x a b b' p
    else
      raise (TranslationError "invalid quantification")
  | UJudge(p, tm, UPi(q, x, a, b)) ->
    let tm' = UApp(p, tm, UCon(p, x, (trans_type a))) in
    translate_abstraction_type ~used x a tm' b p
  | UJudge(p, tm, UImp(q, t1, t2)) ->
    (* fresh_wrt ts tag name ty used *)
    let (x, used) = Term.fresh_wrt
        ~ts:0 Constant lfproof_var (trans_type t1) used in
    let tm' = UApp(p, tm, UCon(p, Term.term_to_name x, (trans_type t1))) in
    translate_abstraction_type ~used (Term.term_to_name x) t1 tm' t2 p
  | UJudge(p, tm, UType(q)) -> is_type (trans_term tm)
  | UJudge(p, t1, t2) -> has_type (trans_term t1) (trans_term t2) p
  | _ -> raise (TranslationError "Only LF judgements may be translated")

and translate_abstraction_type ~used x a t1 t2 pos =
  let aty = trans_type a in
  let l = UJudge(pos, UCon(pos, x, aty), a) in
  let l' = translate ~used l in
  let used = (x, Term.var Constant x 0 aty) :: used in
  let r = UJudge(pos, t1, t2) in
  let r' = translate ~used r in
  (* "forall x, l' => r'" *)
  let tya = trans_type a in
  app (const "pi" (tyarrow [tyarrow [tya] oty] oty))
    [abstract x tya (app (const "=>" (tyarrow [oty; oty] oty)) [l'; r'])]


let lookup_ty x = x (*MKS: still need to implement this *)

let rec lfterm_to_string t cx n =
  let t' = Term.observe t in
  let rec aux tm =
    match tm with
    | Var(v) -> v.name
    | Lam(tyctx, body) ->
      let (vars, tys) = List.split tyctx in
      List.fold_right (fun (v, t) x -> "["^v^":"^(lookup_ty v)^"] ("^x^")")
        tyctx
        (lfterm_to_string body (List.rev_append vars cx) (n+List.length vars))
    | App(h, args) ->
      (match (Term.observe h), args with
       | Var(v), [t1;t2] when v.name="=>" ->
         "("^(aux (Term.observe t1))^")=>("^(aux (Term.observe t2))^")"
       | Var(v), [t1;t2] when v.name="lfhas" ->
         "<("^(aux (Term.observe t1))^"):("^(aux (Term.observe t2))^")>"
       | Var(v), [t] when v.name="lfisty" ->
         "<("^(aux (Term.observe t))^"):type>"
       | Var(v), [t] when v.name="pi" ->
         (match Term.observe t with
          | Lam([(x,ty)], body) ->
            "forall "^x^":"^(Term.ty_to_string ty)^".("^
            (lfterm_to_string body (cx @ [x]) (n+1))^")"
          | _ -> raise (TranslationError "LF terms should not be of this form."))
       | h', _ ->
         List.fold_left (fun x y -> x^" "^y)
           (aux h')
           (List.map (fun x -> aux (Term.observe x)) args))
    | DB i -> (try List.nth cx (i - 1) with _ -> ("x"^string_of_int (n - i + 1)))
    | _ -> raise (TranslationError "terms of this form cannot be inverted.")
  in aux t'
