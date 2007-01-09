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
  
let display (vars, hyps, goal) =
  print_newline () ;
  print_string (vars_to_string vars) ;
  print_newline () ;
  print_string (hyps_to_string hyps) ;
  print_newline () ;
  print_string div ;
  print_string "  "; print_string (lppterm_to_string goal) ;
  print_newline () ;
  print_newline ()

let vars = ref []
let hyps = ref []
let goal = ref (obj (atom "placeholder"))

let add_hyp ?(name=fresh_hyp_name ()) term =
  hyps := List.append !hyps [(name, term)]

let add_var name term =
  vars := List.append !vars [(name, term)]

let get_hyp name =
  List.assoc name !hyps

let get_var name =
  List.assoc name !vars

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
                    Tactics.object_inst stmt (get_var arg)
                | _ -> failwith "Bad application"
              end
      | Case(str) -> ()
      | Search -> ()
      | Theorem(thm) -> goal := thm
      | Intros ->
          let (new_vars, new_hyps, new_goal) = intros !goal in
            List.iter (fun (v, ty) -> add_var v ty) new_vars ;
            List.iter add_hyp new_hyps ;
            goal := new_goal
    end ;
    display (!vars, !hyps, !goal) ;
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

let _ =
  Format.printf "%s%!" welcome_msg ;
  process ~interactive:true (Lexing.from_channel stdin)
