open Term
open Lppterm
open Printf
open Tactics
open Types
open Extensions

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
  { vars = [] ; hyps = [] ; goal = termobj (const "placeholder") ; count = 0 }

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

(* Clauses *)

let parse_clauses str =
  Parser.clauses Lexer.token (Lexing.from_string str)

let clauses : clauses ref = ref (parse_clauses "X = X.")

let add_clauses new_clauses =
  clauses := !clauses @ new_clauses
  
let meta_clauses : clauses ref =
  ref (parse_clauses
         ("X = X." ^
            "member A (A :: L)." ^
            "member A (B :: L) :- member A L."))

let add_meta_clause new_clause =
  meta_clauses := !meta_clauses @ [new_clause]
    
  
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
  let original_meta_clauses = !meta_clauses in
    fun () ->
      reset_prover () ;
      clauses := original_clauses ;
      meta_clauses := original_meta_clauses
      

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

let get_other_subgoals () =
  save_undo_state () ;
  let buffer = Buffer.create 100 in
  let n = ref 1 in
    List.iter (fun set_state ->
                 set_state () ;
                 incr n ;
                 bprintf buffer "subgoal %d is:\n" !n ;
                 bprintf buffer " %s\n\n" (lppterm_to_string sequent.goal))
      !subgoals ;
    undo () ;
    Buffer.contents buffer

let get_display () =
  let buffer = Buffer.create 100 in
    bprintf buffer "%d subgoal(s).\n" (1 + List.length !subgoals) ;
    bprintf buffer "\n" ;
    bprintf buffer "%s\n" (vars_to_string ()) ;
    bprintf buffer "%s\n" (hyps_to_string ()) ;
    bprintf buffer "%s\n" div ;
    bprintf buffer "  %s\n" (lppterm_to_string sequent.goal) ;
    bprintf buffer "\n" ;
    bprintf buffer "%s" (get_other_subgoals ()) ;
    Buffer.contents buffer
    
let display () =
  print_string (get_display ())

    
(* Object level instantiation *)

let inst h n t =
  save_undo_state () ;
  match get_hyp h with
    | Obj(obj, r) ->
        let new_obj = object_inst obj n (replace_term_vars sequent.vars t) in
          add_hyp (Obj(new_obj, r))
    | _ -> failwith "Object cut can only be used on objects"

(* Object level cut *)
    
let cut h arg =
  save_undo_state () ;
  let h = get_hyp h in
  let arg = get_hyp arg in
    match h, arg with
      | Obj(obj_h, _), Obj(obj_arg, _) ->
          add_hyp (object_cut obj_h obj_arg)
      | _ -> failwith "Cut must be used on objects"

          
(* Search *)

let search_goal goal =
  Tactics.search
    ~depth:10
    ~hyps:(List.map snd sequent.hyps)
    ~clauses:!clauses
    ~meta_clauses:!meta_clauses
    ~goal:goal

let search () =
  save_undo_state () ;
  if search_goal sequent.goal then
    next_subgoal ()
  else
    ()

      
(* Apply *)

let get_some_hyp name =
  if name = "_" then
    None
  else
    Some (get_hyp name)
          
let apply h args =
  save_undo_state () ;
  let stmt = get_hyp_or_lemma h in
  let result, obligations =
    match stmt, args with
      | Forall _, _ ->
          apply_forall stmt (List.map get_some_hyp args)
      | _ -> failwith "Apply called on non-forall statement"
  in
    List.iter (fun g ->
                 if not (search_goal (normalize g)) then
                   failwith ("Failed to prove obligation: " ^
                               (lppterm_to_string g)))
      obligations ;
    add_hyp (normalize result)

    
(* Case analysis *)

let set_minus lst1 lst2 =
  List.remove_all (fun x -> List.mem x lst2) lst1

let add_cases_to_subgoals cases =
  let case_to_subgoal case =
    let saved_sequent = copy_sequent () in
      fun () ->
        set_sequent saved_sequent ;
        List.iter add_if_new_var case.new_vars ;
        List.iter add_hyp case.new_hyps ;
        Term.set_bind_state case.bind_state ;
  in
    subgoals := List.append (List.map case_to_subgoal cases) !subgoals

let case str =
  save_undo_state () ;
  let obj = get_hyp str in
  let cases = Tactics.case obj !clauses !meta_clauses (var_names ()) in
    add_cases_to_subgoals cases ;
    next_subgoal ()

      
(* Assert *)
      
let assert_hyp term =
  save_undo_state () ;
  let term = replace_lppterm_vars sequent.vars term in
    add_cases_to_subgoals
      [{ bind_state = get_bind_state () ;
         new_vars = [] ;
         new_hyps = [term] }] ;
    sequent.goal <- term


(* Induction *)

let rec fresh_hyp_name_from_base base =
  if List.mem_assoc base sequent.hyps then
    fresh_hyp_name_from_base (base ^ "'")
  else
    base

let induction args =
  save_undo_state () ;
  let (ih, new_goal) = Tactics.induction args sequent.goal in
  let name = fresh_hyp_name_from_base "IH" in
    add_hyp ~name:name ih ;
    sequent.goal <- new_goal

      
(* Theorem *)

let theorem thm =
  sequent.goal <- thm

    
(* Introduction of forall variables *)

let rec split_args stmt =
  match stmt with
    | Arrow(left, right) ->
        let args, goal = split_args right in
          (left::args, goal)
    | _ -> ([], stmt)

let intros () =
  save_undo_state () ;
  if sequent.vars != [] then
    failwith "Intros can only be used when there are no context variables" ;
  match sequent.goal with
    | Forall(bindings, body) ->
        sequent.vars <- fresh_alist_wrt Eigen bindings (var_names ()) ;
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
