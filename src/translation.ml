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

let signature_lookup sign x =
  try Some (List.assoc x sign)
  with _ -> None

let rec trans_term sign t =
  match t with
  | UCon(p, x, ty0) ->
      let ty = match signature_lookup sign x with
        | None -> ty0
        | Some ty -> ty
      in
      const x ty
  | UApp(p, t1, t2) -> app (trans_term sign t1) [(trans_term sign t2)]
  | UAbs(p, x, a, b) ->
      let xty = trans_type a in
      let sign = (x, xty) :: sign in
      abstract x xty (trans_term sign b)
  | _ -> raise (TranslationError "invalid term")

let lfproof_var = "lf_"
let defaultused : (id * term) list =
  [lfproof_var, Term.var Constant lfproof_var 0 lfobjty]

let rec translate ?(used=defaultused) ~sign t =
  match t with
  | UJudge(p, UAbs(q, x, a, b), UPi(q', x', a', b')) ->
      if x=x' && a= a' then (* MKS: shouldn't this be alpha equiv rather than eq? *)
        translate_abstraction_type ~used ~sign x a b b' p
      else
        raise (TranslationError "invalid quantification")
  | UJudge(p, tm, UPi(q, x, a, b)) ->
      let tm' = UApp(p, tm, UCon(p, x, (trans_type a))) in
      translate_abstraction_type ~used ~sign x a tm' b p
  | UJudge(p, tm, UImp(q, t1, t2)) ->
      (* fresh_wrt ts tag name ty used *)
      let (x, used) = Term.fresh_wrt
          ~ts:0 Constant lfproof_var (trans_type t1) used in
      let tm' = UApp(p, tm, UCon(p, Term.term_to_name x, (trans_type t1))) in
      translate_abstraction_type ~used ~sign (Term.term_to_name x) t1 tm' t2 p
  | UJudge(p, tm, UType(q)) -> is_type (trans_term sign tm)
  | UJudge(p, t1, t2) -> has_type (trans_term sign t1) (trans_term sign t2) p
  | _ ->
      Format.eprintf "ERROR: Could not translate: %a\n@." Uterm.pp_uterm t ;
      raise (TranslationError "Only LF judgements may be translated")

and translate_abstraction_type ~used ~sign x a t1 t2 pos =
  let aty = trans_type a in
  let l = UJudge(pos, UCon(pos, x, aty), a) in
  let l' = translate ~used ~sign l in
  let used = (x, Term.var Constant x 0 aty) :: used in
  let r = UJudge(pos, t1, t2) in
  let r' = translate ~used ~sign r in
  (* "forall x, l' => r'" *)
  let tya = trans_type a in
  app (const "pi" (tyarrow [tyarrow [tya] oty] oty))
    [abstract x tya (app (const "=>" (tyarrow [oty; oty] oty)) [l'; r'])]

and translate_context ?(used=defaultused) ~sign l =
  match l with
  | UCon(p, "nil", _) -> Context.nil
  | UCon(p, g, _) -> const g oty
  | UApp(_, UApp(_, UCon (_, "::", _), uj), ujs) ->
      let t = translate ~used ~sign uj in
      let ts = translate_context ~used ~sign ujs in
      app Context.cons [t; ts]
  | _ ->
      Format.eprintf "ERROR: Could not translate: %a\n@." Uterm.pp_uterm l ;
      raise (TranslationError "Only LF contexts may be translated")

let rec is_vacuous n t =
  match observe (hnorm t) with
  | DB m -> n <> m
  | Var _ -> true
  | App (t, ts) ->
      is_vacuous n t && List.for_all (is_vacuous n) ts
  | Lam (tcx, t) ->
      is_vacuous (n + List.length tcx) t
  | _ -> assert false

let dummy_type = Ty ([], "__dummy")
let dummy_value = const "__dummy" dummy_type
let lftype = const "type" dummy_type
let lfpi = var Constant "__lfpi" 0 dummy_type
let make_lfpi a0 b0 = app lfpi [a0 ; b0]

exception Not_invertible of string
let not_invertible msg = raise (Not_invertible msg)

let unapp t =
  match observe (hnorm t) with
  | App (h, ts) ->
      let (ts, tn) = match List.rev ts with
        | tn :: ts -> (List.rev ts, tn)
        | _ -> assert false
      in
      (app h ts, tn)
  | _ -> not_invertible "unapply"

let lf_printer = object (self)
  inherit term_printer as super
  method print cx t =
    match norm t with
    | App (Var {name="__lfpi"; _}, [a; (Lam ([x, xty], b) as b0)]) ->
        if is_vacuous 1 b then begin
          let b = norm (app b0 [dummy_value]) in
          Pretty.(Opapp (2, Infix (RIGHT, self#print cx a, FMT " ->@ ", self#print cx b)))
        end else begin
          let op = Pretty.(
              Bracket { left = STR "{" ;
                        right = STR "}" ;
                        trans = OPAQUE ;
                        indent = 3 ;
                        inner = Opapp (-1, Infix (NON, Atom (STR x), FMT ":",
                                                  self#print cx a)) })
          in
          Pretty.(Opapp (0, Infix (RIGHT, op, FMT "@ ", self#print ((x, xty) :: cx) b)))
        end
    | Lam ([x, xty], t) ->
        Pretty.(Opapp (1, Prefix (STR ("[" ^ x ^ "] "), self#print ((x, xty) :: cx) t)))
    | _ -> super#print cx t
end

let fresh_x =
  let last = ref 0 in
  fun ty -> incr last ; const ("__lf" ^ string_of_int !last) ty

let rec invert t =
  match t with
  | App (Var {name="lfisty"; _}, [lfty]) ->
      (lfty, lftype)
  | App (Var {name="lfhas"; _}, [lfobj ; lfty]) ->
      (lfobj, lfty)
  | App (Var {name="pi"; _}, [
      Lam ([x, xty], App (Var {name="=>"; _}, [arg; bod]))
    ]) -> begin
      let (arg0, argclass) = invert arg in
      let argclass = norm (app (lambda [x, xty] argclass) [dummy_value]) in
      let (bod0, _bodclass) = invert bod in
      let (_bod, last) = unapp bod0 in
      if eq arg0 last then
        (norm (app (lambda [x, xty] _bod) [dummy_value]),
         make_lfpi argclass (lambda [x, xty] _bodclass))
      else not_invertible "invert 1"
    end
  | _ -> not_invertible "invert 2"

let lf_judge encl u j =
  let open Pretty in
  let inner = Opapp (0, Infix (LEFT, u, FMT ":@,", j)) in
  let (left, right) = if !Flags.annotate then
      (STR_AS (1, "&lt;"), STR_AS (1, "&gt;"))
    else
      (STR "<", STR ">")
  in
  if encl then
    Bracket {
      left ; right ;
      indent = 3 ; trans = OPAQUE ;
      inner ;
    }
  else
    Atom (FUN (fun ff -> print ff inner))

let make_lfjudge_printer encl = object (self)
  inherit term_printer as super
  method print cx t0 =
    let t0 = norm t0 in
    try begin
      let (u, j) = invert t0 in
      lf_judge encl (lf_printer#print cx u) (lf_printer#print cx j)
    end with
    | Not_invertible msg ->
        (* Printf.eprintf "Could not invert [%s]: %s\n%!" msg *)
        (*   (term_to_string ~printer:core_printer ~cx t0) ; *)
        super#print cx t0
end

let lfjudge_printer = make_lfjudge_printer false

let lfterm_to_string t cx n =
  term_to_string ~printer:lfjudge_printer ~cx t

let () = Term.default_printer := make_lfjudge_printer true
