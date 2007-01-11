open Term
open Pprint
open Lppterm

type top_command =
  | Theorem of lppterm

type command =
  | Induction of int list
  | Apply of id * id list
  | Case of id
  | Search
  | Intros

type id = string

type vars = id list
type hyps = (id * lppterm) list

type subgoal = unit -> unit

let vars : vars ref = ref []
let hyps : hyps ref = ref []
let goal : lppterm ref = ref (obj (const "placeholder"))
let subgoals : subgoal list ref = ref []

let count = ref 0

let fresh_hyp_name () =
  incr count ;
  "H" ^ (string_of_int !count)
  
let reset_prover () =
  count := 0 ;
  vars := [] ;
  hyps := [] ;
  goal := obj (const "placeholder") ;
  subgoals := []

type clauses = (lppterm * lppterm list) list
  
let clauses : clauses ref = ref []

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
    | set_subgoal::rest ->
        set_subgoal () ;
        subgoals := rest

let vars_to_string vars =
  match vars with
    | [] -> ""
    | _ -> "  Variables: " ^ (String.concat ", " vars)

let hyps_to_string hyps =
  String.concat "\n"
    (List.map (fun (id, t) -> "  " ^ id ^ " : " ^ (lppterm_to_string t)) hyps)
   
let div = "  ============================\n"

let display () =
  print_int (1 + List.length !subgoals) ;
  print_string " subgoal(s).\n" ;
  print_newline () ;
  print_endline (vars_to_string !vars) ;
  print_endline (hyps_to_string !hyps) ;
  print_string div ;
  print_string "  "; print_endline (lppterm_to_string !goal) ;
  print_newline ()

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
              (* TODO - this is a slight bug, if we recreate the variable
                 like this then it won't be updated if the variable is
                 unified with something else. We should instead find this
                 variable in the context, but we don't yet track the
                 actual variables there *)
              Tactics.object_inst stmt (var ~tag:Eigen arg 0)
            else
              failwith ("Variable not found: " ^ arg)
        | _ -> failwith "Bad application"
      end

(* Case *)

let set_minus lst1 lst2 =
  List.filter (fun x -> not (List.mem x lst2)) lst1

let add_cases_to_subgoals cases =
  let case_to_subgoal (set_state, used_vars, new_hyps) =
    let saved_vars = !vars in
    let saved_hyps = !hyps in
    let saved_goal = !goal in
    let saved_count = !count in
      fun () ->
        vars := saved_vars ;
        hyps := saved_hyps ;
        goal := saved_goal ;
        count := saved_count ;
        List.iter add_if_new_var used_vars ;
        List.iter add_hyp new_hyps ;
        set_state () ;
  in
    subgoals := List.append !subgoals (List.map case_to_subgoal cases)
      
let case str =
  let obj = get_hyp str in
  let cases = Tactics.case obj !clauses !vars in
    match cases with
      | [] -> next_subgoal ()
      | (set_state, used_vars, new_hyps)::other_cases ->
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

let search () =
  if Tactics.search 1 !goal !clauses !vars (List.map snd !hyps) then
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
            
let intros () =
  goal := freshen_bindings !goal !vars ;
  let (new_vars, new_hyps, new_goal) = split_bindings_and_args !goal in
    List.iter add_var new_vars ;
    List.iter add_hyp new_hyps ;
    goal := new_goal
