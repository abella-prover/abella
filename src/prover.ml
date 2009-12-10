(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

open Term
open Typing
open Metaterm
open Format
open Tactics
open Types
open Extensions

module H = Hashtbl

type lemmas = (id * metaterm) list
let lemmas : lemmas ref = ref []

type subgoal = unit -> unit
let subgoals : subgoal list ref = ref []

type hyp = {
  id : id ;
  term : metaterm ;
  mutable abbrev : string option ;
}

type sequent = {
  mutable vars : (id * term) list ;
  mutable hyps : hyp list ;
  mutable goal : metaterm ;
  mutable count : int ;
  mutable name : string ;
  mutable next_subgoal_id : int ;
}

let sequent = {
  vars = [] ;
  hyps = [] ;
  goal = termobj (const "placeholder" propty) ;
  count = 0 ;
  name = "" ;
  next_subgoal_id = 1 ;
}

let sign = ref pervasive_sign

let add_global_types tys =
  sign := add_types !sign tys

let add_global_consts cs =
  sign := add_consts !sign cs

let add_subgoals ?(mainline) new_subgoals =
  let extend_name i =
    if sequent.name = "" then
      sequent.name <- string_of_int i
    else
      sequent.name <- sequent.name ^ "." ^ (string_of_int i)
  in
  let rec annotate i gs =
    match gs with
      | [] -> []
      | g::rest ->
          (fun () -> g (); extend_name i; sequent.next_subgoal_id <- 1) ::
            annotate (i+1) rest
  in
  let n = List.length new_subgoals in
  let annotated_subgoals =
    match mainline with
      | None ->
          if n > 1 then
            annotate sequent.next_subgoal_id new_subgoals
          else
            new_subgoals
      | Some mainline ->
          let new_mainline () =
            mainline () ;
            sequent.next_subgoal_id <- sequent.next_subgoal_id + n
          in
            annotate sequent.next_subgoal_id new_subgoals @ [new_mainline]
  in
    subgoals := annotated_subgoals @ !subgoals

(* The vars = sequent.vars is superfluous, but forces the copy *)
let copy_sequent () =
  {sequent with vars = sequent.vars}

let set_sequent other =
  sequent.vars <- other.vars ;
  sequent.hyps <- other.hyps ;
  sequent.goal <- other.goal ;
  sequent.count <- other.count ;
  sequent.name <- other.name ;
  sequent.next_subgoal_id <- other.next_subgoal_id

let fresh_hyp_name base =
  if base = "" then begin
    sequent.count <- sequent.count + 1 ;
    "H" ^ (string_of_int sequent.count)
  end else
    fresh_name base (List.map (fun h -> (h.id, ())) sequent.hyps)

let normalize_sequent () =
  sequent.goal <- normalize sequent.goal ;
  sequent.hyps <-
    sequent.hyps |> List.map (fun h -> { h with term = normalize h.term })

(* Clauses *)

let clauses : clauses ref = ref []

let add_clauses new_clauses =
  clauses := !clauses @ new_clauses

let parse_defs str =
  type_udefs ~sign:!sign (Parser.defs Lexer.token (Lexing.from_string str))

let defs_table : defs_table = H.create 10
let () = H.add defs_table "member"
  (Inductive,
   ["member"],
   parse_defs "member A (A :: L) ; member A (B :: L) := member A L.")

let add_defs ids ty defs =
  List.iter
    (fun id -> if H.mem defs_table id then
       failwith (id ^ " has already been defined"))
    ids ;
  List.iter
    (fun id -> H.add defs_table id (ty, ids, defs))
    ids


(* Undo support *)

type undo_stack = (sequent * subgoal list * Term.bind_state) list
let undo_stack : undo_stack ref = ref []

let save_undo_state () =
  undo_stack := (copy_sequent (), !subgoals, Term.get_bind_state ())::
    !undo_stack

let undo () =
  match !undo_stack with
    | (saved_sequent, saved_subgoals, bind_state)::rest ->
        set_sequent saved_sequent ;
        subgoals := saved_subgoals ;
        Term.set_bind_state bind_state ;
        undo_stack := rest
    | [] -> failwith "Nothing left to undo"


(* Proof state manipulation utilities *)

let reset_prover =
  let original_sequent = copy_sequent () in
    fun () ->
      set_sequent original_sequent ;
      subgoals := [] ;
      undo_stack := []

let full_reset_prover =
  let original_clauses = !clauses in
  let original_defs_table = H.copy defs_table in
    fun () ->
      reset_prover () ;
      clauses := original_clauses ;
      H.assign defs_table original_defs_table

let add_hyp ?(name=fresh_hyp_name "") term =
  sequent.hyps <- List.append sequent.hyps
    [{ id = name ; term = term ; abbrev = None }]

let remove_hyp name =
  sequent.hyps <- List.remove_all (fun h -> h.id = name) sequent.hyps

let replace_hyp name t =
  let rec aux hyplist =
    match hyplist with
      | [] -> []
      | hyp::rest when hyp.id = name -> {hyp with term = t} :: rest
      | hyp::rest -> hyp :: (aux rest)
  in
    sequent.hyps <- aux sequent.hyps

let add_var v =
  sequent.vars <- List.append sequent.vars [v]

let add_if_new_var (name, v) =
  if not (List.mem_assoc name sequent.vars) then
    add_var (name, v)

let add_lemma name lemma =
  lemmas := (name, lemma)::!lemmas

let get_hyp name =
  let hyp = List.find (fun h -> h.id = name) sequent.hyps in
    hyp.term

let get_lemma name =
  List.assoc name !lemmas

let get_hyp_or_lemma name =
  try
    get_hyp name
  with
      Not_found -> get_lemma name

let next_subgoal () =
  match !subgoals with
    | [] -> failwith "Proof completed."
    | set_subgoal::rest ->
        set_subgoal () ;
        normalize_sequent () ;
        subgoals := rest


(* Pretty print *)

let vars_to_string () =
  match sequent.vars with
    | [] -> ""
    | _ -> "Variables: " ^ (String.concat ", " (List.map fst sequent.vars))

let format_vars fmt =
  let rec aux fmt xs =
    match xs with
      | x::y::ys -> fprintf fmt "%s,@ " (fst x) ; aux fmt (y::ys)
      | [x] -> fprintf fmt "%s" (fst x)
      | [] -> assert false
  in
    if sequent.vars = [] then
      fprintf fmt "@\n"
    else
      fprintf fmt "  Variables: @[%a@]@\n" aux sequent.vars

let format_hyp fmt hyp =
  fprintf fmt "%s : " hyp.id ;
  begin match hyp.abbrev with
    | None -> format_metaterm fmt hyp.term
    | Some s -> fprintf fmt "%s" s
  end;
  pp_force_newline fmt ()

let format_hyps fmt =
  List.iter (format_hyp fmt) sequent.hyps

let format_count_subgoals fmt n =
  match n with
    | 0 -> ()
    | 1 -> fprintf fmt "1 other subgoal.@\n@\n"
    | n -> fprintf fmt "%d other subgoals.@\n@\n" n

let format_display_subgoals fmt n =
  save_undo_state () ;
  let count = ref 0 in
    List.iter (fun set_state ->
                 set_state () ;
                 if String.count sequent.name '.' > n then
                   fprintf fmt "@[<1>Subgoal %s%sis:@\n%a@]@\n@\n"
                     sequent.name
                     (if sequent.name = "" then "" else " ")
                     format_metaterm (normalize sequent.goal)
                 else
                   incr count)
      !subgoals ;
    format_count_subgoals fmt !count ;
    undo ()

let subgoal_depth = ref 1000

let format_other_subgoals fmt =
  format_display_subgoals fmt (String.count sequent.name '.' - !subgoal_depth)

let format_sequent fmt =
  pp_open_box fmt 2 ;
  format_vars fmt ;
  format_hyps fmt ;
  fprintf fmt "============================@\n" ;
  fprintf fmt " %a" format_metaterm sequent.goal ;
  pp_close_box fmt ()

let format_display fmt =
  pp_open_box fmt 0 ;
  if sequent.name = "" then
    fprintf fmt "@\n"
  else
    fprintf fmt "Subgoal %s:@\n@\n" sequent.name;
  format_sequent fmt ;
  fprintf fmt "@\n@\n" ;
  format_other_subgoals fmt ;
  pp_close_box fmt () ;
  pp_print_flush fmt ()

let display out =
  format_display (formatter_of_out_channel out)

let get_display () =
  let b = Buffer.create 100 in
    format_display (formatter_of_buffer b) ;
    Buffer.contents b


(* Object level instantiation *)

let inst h n t =
  let ht = get_hyp h in
    match ht with
      | Obj _ ->
          begin try
            let ntids = metaterm_nominal_tids ht in
            let nty = List.assoc n ntids in
            let ctx = sequent.vars @
              (List.map (fun (id, ty) -> (id, nominal_var id ty)) ntids)
            in
            let t = type_uterm ~sign:!sign ~ctx t nty in
              add_hyp (object_inst ht n t)
          with
            | Not_found ->
                failwith "Vacuous instantiation"
          end
      | _ -> failwith
          "Instantiation can only be used on hypotheses of the form {...}"


(* Object level cut *)

let cut h arg =
  let h = get_hyp h in
  let arg = get_hyp arg in
    match h, arg with
      | Obj(obj_h, _), Obj(obj_arg, _) ->
          add_hyp (object_cut obj_h obj_arg)
      | _ -> failwith "Cut can only be used on hypotheses of the form {...}"


(* Search *)

let has_inductive_hyps hyp =
  let rec aux term =
    match term with
      | Binding(Forall, _, body) -> aux body
      | Binding(Nabla, _, body) -> aux body
      | Arrow(Obj(_, Smaller i), _) -> true
      | Arrow(Pred(_, Smaller i), _) -> true
      | Arrow(left, right) -> aux right
      | _ -> false
  in
    aux hyp.term

let remove_inductive_hypotheses hyps =
  List.remove_all has_inductive_hyps hyps

let has_coinductive_result hyp =
  let rec aux term nested =
    match term with
      | Binding(Forall, _, body) -> aux body true
      | Binding(Nabla, _, body) -> aux body true
      | Arrow(left, right) -> aux right true
      | Pred(_, CoSmaller _) -> nested
      | Pred(_, CoEqual _) -> nested
      | _ -> false
  in
    aux hyp.term false

let remove_coinductive_hypotheses hyps =
  List.remove_all has_coinductive_result hyps

let defs_table_to_list () =
  H.fold (fun _ (_, mutual, dcs) acc -> (mutual, dcs) :: acc) defs_table []

let search_goal_witness ?(depth=5) goal =
  let hyps = sequent.hyps
    |> remove_inductive_hypotheses
    |> remove_coinductive_hypotheses
    |> List.map (fun h -> (h.id, h.term))
  in
  let search_depth n =
    Tactics.search
      ~depth:n
      ~hyps
      ~clauses:!clauses
      ~alldefs:(defs_table_to_list ())
      goal
  in
    List.find_some search_depth (List.range 1 depth)

let search_goal goal =
  Option.is_some (search_goal_witness goal)

let search ?(limit=None) ?(interactive=true) ?(witness=ignore) () =
  let search_result = match limit with
    | None -> search_goal_witness sequent.goal
    | Some depth -> search_goal_witness ~depth sequent.goal
  in
    match search_result with
      | None -> if not interactive then failwith "Search failed"
      | Some w -> witness w ; next_subgoal ()

(* Apply *)

let get_some_hyp name =
  if name = "_" then
    None
  else
    Some (get_hyp name)

let goal_to_subgoal g =
  let saved_sequent = copy_sequent () in
  let bind_state = Term.get_bind_state () in
    fun () ->
      set_sequent saved_sequent ;
      Term.set_bind_state bind_state ;
      sequent.goal <- g

let ensure_no_logic_variable terms =
  let logic_vars = List.flatten_map (metaterm_vars_alist Logic) terms in
  if logic_vars <> [] then
    failwith "Found logic variable at toplevel"

let ensure_no_restrictions term =
  let rec aux t nested =
    match t with
      | Binding(Forall, _, body) -> aux body true
      | Binding(Nabla, _, body) -> aux body true
      | Arrow(left, right) -> aux left true; aux right true
      | Obj(_, Smaller i) | Obj(_, Equal i)
      | Pred(_, Smaller i) | Pred(_, Equal i) ->
          if nested then invalid_metaterm_arg term
      | Pred(_, CoSmaller i) | Pred(_, CoEqual i) ->
          invalid_metaterm_arg term
      | _ -> ()
  in
    aux term false

let toplevel_bindings stmt =
  let rec aux = function
    | Binding(Forall, tids, t) -> tids @ (aux t)
    | Binding(Nabla, tids, t) -> tids @ (aux t)
    | _ -> []
  in
    aux stmt

(* TODO: Typing the nominals in a 'with' is still a quesiton *)
let type_apply_withs stmt ws =
  let bindings = toplevel_bindings stmt in
    List.map
      (fun (id, t) ->
         try
           let ty = List.assoc id bindings in
             (id, type_uterm ~sign:!sign ~ctx:sequent.vars t ty)
         with
           | Not_found -> failwith ("Unknown variable " ^ id ^ "."))
      ws

let apply h args ws =
  let stmt = get_hyp_or_lemma h in
  let args = List.map get_some_hyp args in
  let () = List.iter (Option.map_default ensure_no_restrictions ()) args in
  let ws = type_apply_withs stmt ws in
  let result, obligations = Tactics.apply_with stmt args ws in
  let remaining_obligations =
    List.remove_all (fun g -> search_goal (normalize g)) obligations in
  let () = ensure_no_logic_variable (result :: remaining_obligations) in
  let obligation_subgoals = List.map goal_to_subgoal remaining_obligations in
  let resulting_case = recursive_metaterm_case ~used:sequent.vars result in
    begin match resulting_case with
      | None -> add_subgoals obligation_subgoals
      | Some case ->
          let resulting_subgoal =
            let restore = goal_to_subgoal sequent.goal in
              fun () ->
                restore () ;
                List.iter add_if_new_var case.stateless_new_vars ;
                List.iter add_hyp case.stateless_new_hyps
          in
            add_subgoals ~mainline:resulting_subgoal obligation_subgoals
    end ;
    next_subgoal ()

(* Bachchain *)

let type_backchain_withs stmt ws =
  let bindings = toplevel_bindings stmt in
  let nctx = List.map term_to_pair (metaterm_support sequent.goal) in
    List.map
      (fun (id, t) ->
         try
           let ty = List.assoc id bindings in
             (id, type_uterm ~sign:!sign ~ctx:(nctx @ sequent.vars) t ty)
         with
           | Not_found -> failwith ("Unknown variable " ^ id ^ "."))
      ws

let backchain h ws =
  let stmt = get_hyp_or_lemma h in
  let ws = type_backchain_withs stmt ws in
  let obligations = Tactics.backchain_with stmt ws sequent.goal in
  let remaining_obligations =
    List.remove_all (fun g -> search_goal (normalize g)) obligations in
  let () = ensure_no_logic_variable remaining_obligations in
  let obligation_subgoals = List.map goal_to_subgoal remaining_obligations in
    add_subgoals obligation_subgoals ;
    next_subgoal ()

(* Case analysis *)

(* Lifting during case analysis may cause some variables to be bound to
   themselves. We need to update sequent.vars to reflect this. *)
let update_self_bound_vars () =
  sequent.vars <-
    sequent.vars |> List.map
        (fun (id, term) ->
           match term_head_var term with
             | Some v when term_to_name v = id ->
                 (id, v)
             | _ -> (id, term))

let case_to_subgoal case =
  let saved_sequent = copy_sequent () in
    fun () ->
      set_sequent saved_sequent ;
      List.iter add_if_new_var case.new_vars ;
      List.iter add_hyp case.new_hyps ;
      Term.set_bind_state case.bind_state ;
      update_self_bound_vars ()

let get_defs term =
  match term with
    | Pred(p, _) ->
        begin try
          let (_, mutual, defs) = H.find defs_table (term_head_name p) in
            (mutual, defs)
        with Not_found ->
          failwith "Cannot perform case-analysis on undefined atom"
        end
    | _ -> ([], [])

let case ?(keep=false) str =
  let term = get_hyp str in
  let global_support =
    (List.flatten_map metaterm_support
       (List.map (fun h -> h.term) sequent.hyps)) @
      (metaterm_support sequent.goal)
  in
  let (mutual, defs) = get_defs term in
  let cases =
    Tactics.case ~used:sequent.vars ~clauses:!clauses
      ~mutual ~defs ~global_support term
  in
    if not keep then remove_hyp str ;
    add_subgoals (List.map case_to_subgoal cases) ;
    next_subgoal ()


(* Induction *)

let get_restriction r =
  match r with
    | Smaller n -> n
    | CoSmaller n -> n
    | Equal n -> n
    | CoEqual n -> n
    | Irrelevant -> 0

let get_max_restriction t =
  let rec aux t =
    match t with
      | True | False | Eq _ -> 0
      | Obj(_, r) -> get_restriction r
      | Arrow(a, b) -> max (aux a) (aux b)
      | Binding(_, _, body) -> aux body
      | Or(a, b) -> max (aux a) (aux b)
      | And(a, b) -> max (aux a) (aux b)
      | Pred(_, r) -> get_restriction r
  in
    aux t

let next_restriction () =
  1 + (sequent.hyps |> List.map (fun h -> h.term) |>
           List.map get_max_restriction |> List.max)

let rec nth_product n term =
  match term with
    | Binding(Forall, _, body) -> nth_product n body
    | Binding(Nabla, _, body) -> nth_product n body
    | Arrow(left, right) ->
        if n = 1 then
          left
        else
          nth_product (n-1) right
    | _ -> failwith "Can only induct on predicates and judgments"

let ensure_is_inductive term =
  match term with
    | Obj _ -> ()
    | Pred(p, _) ->
        let pname = term_head_name p in
          begin try
            match H.find defs_table pname with
              | Inductive, _, _ -> ()
              | CoInductive, _, _ -> failwith
                  (sprintf "Cannot induct on %s since it has\
                          \ been coinductively defined" pname)
          with Not_found ->
            failwith (sprintf "Cannot induct on %s since it has\
                             \ not been defined" pname)
          end
    | _ -> failwith "Can only induct on predicates and judgments"

let add_ih h =
  add_hyp ~name:(fresh_hyp_name "IH") h

let induction ind_args =
  if has_coinductive_restriction sequent.goal then
    failwith "Induction within coinduction is not allowed" ;
  List.iter
    (fun (arg, goal) -> ensure_is_inductive (nth_product arg goal))
    (List.combine ind_args (and_to_list sequent.goal)) ;
  let res_num = next_restriction () in
    let (ihs, new_goal) = Tactics.induction ind_args res_num sequent.goal in
      List.iter (fun h -> add_hyp ~name:(fresh_hyp_name "IH") h) ihs ;
      sequent.goal <- new_goal


(* CoInduction *)

let rec conclusion term =
  match term with
    | Binding(Forall, _, body) -> conclusion body
    | Binding(Nabla, _, body) -> conclusion body
    | Arrow(left, right) -> conclusion right
    | Pred(p, _) -> p
    | _ -> failwith "Cannot coinduct on a goal of this form"

let ensure_is_coinductive p =
  let pname = term_head_name p in
    try
      match H.find defs_table pname with
        | CoInductive, _, _ -> ()
        | Inductive, _, _ -> failwith
            (sprintf "Cannot coinduct on %s since it has\
                    \ been inductively defined" pname)
    with Not_found ->
      failwith (sprintf "Cannot coinduct on %s since it has\
                       \ not been defined" pname)

let coinduction () =
  ensure_is_coinductive (conclusion sequent.goal) ;
  if has_inductive_restriction sequent.goal then
    failwith "Coinduction within induction is not allowed" ;
  let res_num = next_restriction () in
  let (ch, new_goal) = Tactics.coinduction res_num sequent.goal in
  let name = fresh_hyp_name "CH" in
    add_hyp ~name ch ;
    sequent.goal <- new_goal


(* Assert *)

let delay_mainline new_hyp detour_goal =
  if search_goal detour_goal then
    add_hyp new_hyp
  else
    let mainline =
      case_to_subgoal { bind_state = get_bind_state () ;
                        new_vars = [] ;
                        new_hyps = [new_hyp] }
    in
    let detour = goal_to_subgoal detour_goal in
      (* Using add_subgoals to take care of annotations *)
      add_subgoals ~mainline [detour] ;
      next_subgoal ()

let assert_hyp term =
  let term = type_umetaterm ~sign:!sign ~ctx:sequent.vars term in
    delay_mainline term term

(* Object logic monotone *)

let monotone h t =
  let ht = get_hyp h in
    match ht with
      | Obj(obj, r) ->
          let ntids = metaterm_nominal_tids ht in
          let ctx = sequent.vars @
            (List.map (fun (id, ty) -> (id, nominal_var id ty)) ntids)
          in
          let t = type_uterm ~sign:!sign ~ctx t olistty in
          let new_obj = { obj with context = Context.normalize [t] } in
            delay_mainline
              (Obj(new_obj, r))
              (Binding(Forall, [("X", oty)],
                       Arrow(member (Term.const "X" oty)
                               (Context.context_to_term obj.context),
                             member (Term.const "X" oty)
                               t))) ;
      | _ -> failwith
          "Monotone can only be used on hypotheses of the form {...}"


(* Theorem *)

let theorem thm =
  sequent.goal <- thm


(* Introduction of forall variables *)

let intros () =
  let rec aux term =
    match term with
      | Binding(Forall, bindings, body) ->
          let support = metaterm_support body in
          let (alist, vars) =
            fresh_raised_alist ~tag:Eigen ~used:sequent.vars ~support bindings
          in
            List.iter add_var (List.map term_to_pair vars) ;
              aux (replace_metaterm_vars alist body)
      | Binding(Nabla, bindings, body) ->
          let (ids, tys) = List.split bindings in
            aux (replace_metaterm_vars
                   (List.combine ids (fresh_nominals tys body))
                   body)
      | Arrow(left, right) ->
          add_hyp (normalize left) ;
          aux right
      | _ -> term
  in
    sequent.goal <- aux sequent.goal

(* Split *)

let split propogate_result =
  let rec accum_goals conjs prev =
    match conjs with
      | [] -> []
      | g::rest ->
          let saved = goal_to_subgoal g in
          let subgoal () =
            saved () ;
            if propogate_result then List.iter add_hyp (List.rev prev)
          in
            subgoal :: (accum_goals rest (g :: prev))
  in
  let conjs = and_to_list sequent.goal in
    if List.length conjs = 1 then failwith "Needless use of split" ;
    add_subgoals (accum_goals (and_to_list sequent.goal) []) ;
    next_subgoal ()

(* Left and right side of disjunction *)

let left () =
  match sequent.goal with
    | Or(left, _) -> sequent.goal <- left
    | _ -> ()

let right () =
  match sequent.goal with
    | Or(_, right) -> sequent.goal <- right
    | _ -> ()


(* Unfold *)

let unfold () =
  let mdefs = get_defs sequent.goal in
  let goal = unfold ~mdefs sequent.goal in
  let goals = and_to_list goal in
    add_subgoals (List.map goal_to_subgoal goals) ;
    next_subgoal ()

(* Exists *)

let exists t =
  match sequent.goal with
    | Binding(Metaterm.Exists, (id, ty)::tids, body) ->
        let ntids = metaterm_nominal_tids body in
        let ctx = sequent.vars @
          (List.map (fun (id, ty) -> (id, nominal_var id ty)) ntids)
        in
        let t = type_uterm ~sign:!sign ~ctx t ty in
        let goal = exists tids (replace_metaterm_vars [(id, t)] body) in
          sequent.goal <- goal
    | _ -> ()

(* Skip *)

let skip () =
  next_subgoal ()

(* Clear *)

let clear hs =
  List.iter remove_hyp hs

(* Abbrev *)

let abbrev id str =
  List.iter (fun h -> if h.id = id then h.abbrev <- Some str) sequent.hyps

let unabbrev ids =
  List.iter (fun h -> if List.mem h.id ids then h.abbrev <- None) sequent.hyps

(* Permute *)

let permute_nominals ids form =
  if not (List.is_unique ids) then failwith "Not a permutation" ;
  let term =
    match form with
      | None -> sequent.goal
      | Some h -> get_hyp h
  in
  let support_alist =
    List.map (fun t -> (term_to_name t, t)) (metaterm_support term)
  in
  let perm =
    List.map
      (fun id ->
         try
           List.assoc id support_alist
         with Not_found -> nominal_var id (tybase ""))
      ids
  in
  let result = Tactics.permute_nominals perm term in
    match form with
      | None -> sequent.goal <- result
      | Some hyp -> replace_hyp hyp result
