open Term
open Pprint
open Lppterm
open Printf

type top_command =
  | Theorem of id * lppterm

type command =
  | Induction of int
  | Apply of id * id list
  | Inst of id * term
  | Case of id
  | Search
  | Intros
  | Skip
  | Undo

type id = string

type lemmas = (id * lppterm) list
let lemmas : lemmas ref = ref []

type subgoal = unit -> unit
let subgoals : subgoal list ref = ref []
  
type sequent = {
  mutable vars : (id * term) list ;
  mutable hyps : (id * lppterm) list ;
  mutable goal : lppterm ;
  mutable count : int ;
}
    
let sequent =
  { vars = [] ; hyps = [] ; goal = obj (const "placeholder") ; count = 0 }

(* The vars = sequent.vars is superfluous, but forces the copy *)
let copy_sequent () =
  {sequent with vars = sequent.vars}

let set_sequent other =
  sequent.vars <- other.vars ;
  sequent.hyps <- other.hyps ;
  sequent.goal <- other.goal ;
  sequent.count <- other.count
    
let var_names () =
  List.map fst sequent.vars

let fresh_hyp_name () =
  sequent.count <- sequent.count + 1 ;
  "H" ^ (string_of_int sequent.count)
  
type clauses = (lppterm * lppterm list) list
let clauses : clauses ref = ref []


(* Undo support *)
  
type undo_stack = (sequent * subgoal list * Term.bind_state) list
let undo_stack : undo_stack ref = ref []
  
let save_undo_state () =
  undo_stack := (copy_sequent (), !subgoals, Term.save_state ())::
    !undo_stack
    
let undo () =
  match !undo_stack with
    | (saved_sequent, saved_subgoals, saved_term_state)::rest ->
        set_sequent saved_sequent ;
        subgoals := saved_subgoals ;
        Term.restore_state saved_term_state ;
        undo_stack := rest
    | [] -> failwith "Nothing left to undo"

        
(* Proof state manipulation utilities *)

let reset_prover =
  let original_sequent = copy_sequent () in
    fun () ->
      set_sequent original_sequent ;
      subgoals := [] ;
      undo_stack := []

let add_hyp ?(name=fresh_hyp_name ()) term =
  sequent.hyps <- List.append sequent.hyps [(name, term)]

let add_var v =
  sequent.vars <- List.append sequent.vars [v]

let add_if_new_var (name, v) =
  if not (List.mem name (var_names ())) then add_var (name, v)

let add_lemma name lemma =
  lemmas := (name, lemma)::!lemmas

let get_hyp name =
  List.assoc name sequent.hyps

let get_lemma name =
  List.assoc name !lemmas

let get_hyp_or_lemma name =
  if List.mem_assoc name sequent.hyps then
    get_hyp name
  else
    get_lemma name

let next_subgoal () =
  match !subgoals with
    | [] -> failwith "Proof completed."
    | set_subgoal::rest ->
        set_subgoal () ;
        subgoals := rest

          
(* Pretty print *)
          
let vars_to_string () =
  match sequent.vars with
    | [] -> ""
    | _ -> "  Variables: " ^ (String.concat ", " (var_names ()))

let hyps_to_string () =
  String.concat "\n"
    (List.map
       (fun (id, t) -> "  " ^ id ^ " : " ^ (lppterm_to_string t))
       sequent.hyps)
   
let div = "  ============================"

let get_display () =
  let buffer = Buffer.create 100 in
    bprintf buffer "%d subgoal(s).\n" (1 + List.length !subgoals) ;
    bprintf buffer "\n" ;
    bprintf buffer "%s\n" (vars_to_string ()) ;
    bprintf buffer "%s\n" (hyps_to_string ()) ;
    bprintf buffer "%s\n" div ;
    bprintf buffer "  %s\n" (lppterm_to_string sequent.goal) ;
    bprintf buffer "\n" ;
    Buffer.contents buffer
    
let display () =
  print_string (get_display ())

    
(* Object level instantiation *)

let inst h t =
  save_undo_state () ;
  let stmt = get_hyp h in
    if Tactics.is_pi_abs (obj_to_term stmt) then
      add_hyp (Tactics.object_inst stmt
                 (replace_term_vars sequent.vars t))
    else
      failwith ("Hypothesis must have the form {pi x\\ ...} " ^
                  "in order to instantiate it with a term.")

        
(* Apply *)
          
let apply h args =
  save_undo_state () ;
  let stmt = get_hyp_or_lemma h in
    add_hyp
      begin match stmt, args with
        | Forall _, _ ->
            Tactics.apply_forall stmt (List.map get_hyp args)
        | Obj(t, _), [arg] when Tactics.is_imp t ->
            Tactics.object_cut stmt (get_hyp arg)
        | _ -> failwith "Bad application"
      end

      
(* Case analysis *)

let set_minus lst1 lst2 =
  List.filter (fun x -> not (List.mem x lst2)) lst1

let add_cases_to_subgoals cases =
  let case_to_subgoal (set_state, used_vars, new_hyps) =
    let saved_sequent = copy_sequent () in
      fun () ->
        set_sequent saved_sequent ;
        List.iter add_if_new_var used_vars ;
        List.iter add_hyp new_hyps ;
        set_state () ;
  in
    subgoals := List.append (List.map case_to_subgoal cases) !subgoals
      
let case str =
  save_undo_state () ;
  let obj = get_hyp str in
  let cases = Tactics.case obj !clauses (var_names ()) in
    match cases with
      | [] -> next_subgoal ()
      | (set_state, used_vars, new_hyps)::other_cases ->
          add_cases_to_subgoals other_cases ;
          List.iter add_if_new_var used_vars ;
          set_state () ;
          List.iter add_hyp new_hyps

            
(* Induction *)
            
let induction args =
  save_undo_state () ;
  let (ih, new_goal) = Tactics.induction args sequent.goal in
    add_hyp ~name:"IH" ih ;
    sequent.goal <- new_goal

      
(* Search *)

let search () =
  save_undo_state () ;
  if Tactics.search 5 sequent.goal !clauses
    (var_names ()) (List.map snd sequent.hyps) then
    next_subgoal ()
  else
    ()

      
(* Theorem *)

let theorem thm =
  sequent.goal <- thm

    
(* Introduction of forall variables *)

let rec split_args stmt =
  match stmt with
    | Arrow(left, right) ->
        let args, goal = split_args right in
          (left::args, goal)
    | Obj _
    | Or(_, _) -> ([], stmt)
    | _ -> invalid_lppterm_arg stmt

let intros () =
  save_undo_state () ;
  if sequent.vars != [] then
    failwith "Intros can only be used when there are no context variables" ;
  match sequent.goal with
    | Forall(bindings, body) ->
        sequent.vars <- Tactics.fresh_alist Eigen bindings (var_names ()) ;
        let fresh_body = replace_lppterm_vars sequent.vars body in
        let args, new_goal = split_args fresh_body in
          List.iter add_hyp args ;
          sequent.goal <- new_goal
    | _ ->
        let args, new_goal = split_args sequent.goal in
          List.iter add_hyp args ;
          sequent.goal <- new_goal

            
(* Skip *)

let skip () =
  save_undo_state () ;
  next_subgoal ()
