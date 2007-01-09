open Term
open Pprint
open Lppterm
open Command

type id = string
    
type vars = (id * term) list
type hyps = (id * lppterm) list

type state = vars * hyps * lppterm
    
let fresh_hyp_name =
  let count = ref 0 in
    fun () ->
      incr count ;
      "H" ^ (string_of_int !count)

let vars_to_string vars =
  String.concat "\n"
    (List.map (fun (id, t) -> "  " ^ id ^ " : " ^ (term_to_string t)) vars)

let hyps_to_string hyps =
  String.concat "\n"
    (List.map (fun (id, t) -> "  " ^ id ^ " : " ^ (lppterm_to_string t)) hyps)
   
let div = "  ============================\n"
  
let vars = ref []
let hyps = ref []
let goal = ref (obj (atom "placeholder"))

let subgoals = ref []

(* This function tells ocaml that the first argument in a subgoal
   has type unit -> unit *)
let force_typing () =
  match !subgoals with
    | (f, _, _, _)::_ -> f ()
    | _ -> ()

let clauses = ref []

let add_hyp ?(name=fresh_hyp_name ()) term =
  hyps := List.append !hyps [(name, term)]

let add_var name term =
  vars := List.append !vars [(name, term)]

let get_hyp name =
  List.assoc name !hyps

let get_var name =
  List.assoc name !vars

let add_cases_to_subgoals cases =
  let case_to_subgoal (set_state, new_hyps) =
    let labeled_hyps = List.map (fun h -> (fresh_hyp_name (), h)) new_hyps in
      (set_state, !vars, List.append !hyps labeled_hyps, !goal)
  in
    subgoals := List.append !subgoals (List.map case_to_subgoal cases)

let next_subgoal () =
  match !subgoals with
    | [] -> failwith "Proof completed."
    | (set_state, next_vars, next_hyps, next_goal)::rest ->
        set_state () ;
        vars := next_vars ;
        hyps := next_hyps ;
        goal := next_goal ;
        subgoals := rest

let display () =
  print_int (1 + List.length !subgoals) ;
  print_string " subgoal(s).\n" ;
  print_newline () ;
  print_endline (vars_to_string !vars) ;
  print_endline (hyps_to_string !hyps) ;
  print_string div ;
  print_string "  "; print_endline (lppterm_to_string !goal) ;
  print_newline ()
        
let welcome_msg = "Lambda Prolog Prover 0.1\n"

let rec split_args stmt =
  match stmt with
    | Arrow(left, right) ->
        let args, goal = split_args right in
          (left::args, goal)
    | Obj _ -> ([], stmt)
    | Forall _ -> failwith "Forall found in split_args"

let intros stmt =
  match stmt with
    | Forall(bindings, body) ->
        let args, goal = split_args body in
          (bindings, args, goal)
    | _ ->
        let args, goal = split_args stmt in
          ([], args, goal)

let obj_match t1 t2 =
  match t1, t2 with
    | Obj(t1, _), Obj(t2, _) -> eq t1 t2
    | _ -> false

let search () =
  if List.exists (obj_match !goal) (List.map snd !hyps) then
    next_subgoal ()
  else
    ()
  
let rec process ?(interactive=true) lexbuf =
  try while true do try
    if interactive then Format.printf "LPP < %!" ;
    begin match Parser.command Lexer.token lexbuf with
      | Induction(args) ->
          let (ih, new_goal) = Tactics.induction args !goal in
            add_hyp ~name:"IH" ih ;
            goal := new_goal
      | Apply(h, args) ->
          let stmt = get_hyp h in
            add_hyp
              begin match stmt, args with
                | Forall _, _ ->
                    Tactics.apply_forall stmt (List.map get_hyp args)
                | Obj(t, _), [arg] when Tactics.is_imp t ->
                    Tactics.object_cut stmt (get_hyp arg)
                | Obj(t, _), [arg] when Tactics.is_pi_abs t ->
                    (* TODO - we should always be able to find this
                       in the vars, but right now the vars doesn't get
                       updated after performing case *)
                    Tactics.object_inst stmt (atom ~tag:Eigen arg)
                | _ -> failwith "Bad application"
              end
      | Case(str) ->
          let obj = get_hyp str in
          let cases = Tactics.case obj !clauses in
            begin match cases with
              | [] -> next_subgoal ()
              | (set_state, new_hyps)::other_cases ->
                  add_cases_to_subgoals other_cases ;
                  set_state () ;
                  List.iter add_hyp new_hyps
            end
      | Search -> search ()
      | Theorem(thm) -> goal := thm
      | Intros ->
          let (new_vars, new_hyps, new_goal) = intros !goal in
            List.iter (fun (v, ty) -> add_var v ty) new_vars ;
            List.iter add_hyp new_hyps ;
            goal := new_goal
    end ;
    display () ;
    if interactive then flush stdout
  with
    | Failure "lexing: empty token" ->
        exit (if interactive then 0 else 1)
    | Failure s ->
        Format.printf "Error: %s\n" s
    | e ->
        Format.printf "Unknown error: %s\n%!" (Printexc.to_string e)
  done with
  | Failure "eof" -> ()

let usage_message = ""
  
let _ =
  Arg.parse []
    (fun file_name ->
       clauses :=
         List.append (Parser.clauses Lexer.token
                        (Lexing.from_channel (open_in file_name)))
           !clauses)
    usage_message ;
  Pprint.set_infix [("=>", Pprint.Right)] ;
  Format.printf "%s%!" welcome_msg ;
  process ~interactive:true (Lexing.from_channel stdin)
