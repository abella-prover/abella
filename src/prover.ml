open Term
open Pprint
open Lppterm

type command =
  | Induction of int list
  | Apply of id * id list
  | Case of id
  | Search
  | Theorem of lppterm
  | Intros

type id = string

type vars = id list
type hyps = (id * lppterm) list

type subgoal = (unit -> unit) * vars * hyps * lppterm

let vars : vars ref = ref []
let hyps : hyps ref = ref []
let goal : lppterm ref = ref (obj (atom "placeholder"))
let subgoals : subgoal list ref = ref []

type clauses = (lppterm * lppterm list) list
  
let clauses : clauses ref = ref []

let fresh_hyp_name =
  let count = ref 0 in
    fun () ->
      incr count ;
      "H" ^ (string_of_int !count)

let add_hyp ?(name=fresh_hyp_name ()) term =
  hyps := List.append !hyps [(name, term)]

let add_var name =
  vars := List.append !vars [name]

let add_if_new_var name =
  if not (List.mem name !vars) then add_var name

let get_hyp name =
  List.assoc name !hyps

let next_subgoal () =
  match !subgoals with
    | [] -> failwith "Proof completed."
    | (set_state, next_vars, next_hyps, next_goal)::rest ->
        set_state () ;
        vars := next_vars ;
        hyps := next_hyps ;
        goal := next_goal ;
        subgoals := rest

(* Apply *)
          
let apply h args =
  let stmt = get_hyp h in
    add_hyp
      begin match stmt, args with
        | Forall _, _ ->
            Tactics.apply_forall stmt (List.map get_hyp args)
        | Obj(t, _), [arg] when Tactics.is_imp t ->
            Tactics.object_cut stmt (get_hyp arg)
        | Obj(t, _), [arg] when Tactics.is_pi_abs t ->
            if List.mem arg !vars then
              Tactics.object_inst stmt (atom ~tag:Eigen arg)
            else
              failwith ("Variable not found: " ^ arg)
        | _ -> failwith "Bad application"
      end

(* Case *)

let set_minus lst1 lst2 =
  List.filter (fun x -> not (List.mem x lst2)) lst1

let add_cases_to_subgoals cases =
  let case_to_subgoal (set_state, used_vars, new_hyps) =
    let labeled_hyps = List.map (fun h -> (fresh_hyp_name (), h)) new_hyps in
    let new_vars = set_minus used_vars !vars in
      (set_state,
       List.append !vars new_vars,
       List.append !hyps labeled_hyps,
       !goal)
  in
    subgoals := List.append !subgoals (List.map case_to_subgoal cases)
      
let case str used =
  let obj = get_hyp str in
  let cases = Tactics.case obj !clauses used in
    match cases with
      | [] -> next_subgoal ()
      | (set_state, used_vars, new_hyps)::other_cases ->
          reset_namespace_except used_vars ;
          add_cases_to_subgoals other_cases ;
          List.iter add_if_new_var used_vars ;
          set_state () ;
          List.iter add_hyp new_hyps

(* Induction *)
            
let induction args =
  let (ih, new_goal) = Tactics.induction args !goal in
    add_hyp ~name:"IH" ih ;
    goal := new_goal

(* Search *)

let obj_match t1 t2 =
  match t1, t2 with
    | Obj(t1, _), Obj(t2, _) -> eq t1 t2
    | _ -> false

let search () =
  if List.exists (obj_match !goal) (List.map snd !hyps) then
    next_subgoal ()
  else
    ()

(* Theorem *)

let theorem thm =
  goal := thm

(* Intros *)

let rec split_args stmt =
  match stmt with
    | Arrow(left, right) ->
        let args, goal = split_args right in
          (left::args, goal)
    | Obj _ -> ([], stmt)
    | Forall _ -> failwith "Forall found in split_args"

let split_bindings_and_args stmt =
  match stmt with
    | Forall(bindings, body) ->
        let args, goal = split_args body in
          (bindings, args, goal)
    | _ ->
        let args, goal = split_args stmt in
          ([], args, goal)

let freshen_bindings stmt used =
  match stmt with
    | Forall(bindings, body) ->
        forall bindings
          (Tactics.replace_vars
             (Tactics.fresh_alist_wrt Eigen bindings used) body)
    | _ -> stmt
            
let intros used =
  goal := freshen_bindings !goal used ;
  let (new_vars, new_hyps, new_goal) = split_bindings_and_args !goal in
    List.iter add_var new_vars ;
    List.iter add_hyp new_hyps ;
    goal := new_goal
