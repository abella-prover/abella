open Term
open Lppterm
open Format
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

let sequent = {
  vars = [] ;
  hyps = [] ;
  goal = termobj (const "placeholder") ;
  count = 0 ;
}

(* The vars = sequent.vars is superfluous, but forces the copy *)
let copy_sequent () =
  {sequent with vars = sequent.vars}

let set_sequent other =
  sequent.vars <- other.vars ;
  sequent.hyps <- other.hyps ;
  sequent.goal <- other.goal ;
  sequent.count <- other.count

let fresh_hyp_name () =
  sequent.count <- sequent.count + 1 ;
  "H" ^ (string_of_int sequent.count)

(* Clauses *)

let parse_clauses str =
  Parser.clauses Lexer.token (Lexing.from_string str)

let clauses : clauses ref = ref (parse_clauses "X = X.")

let add_clauses new_clauses =
  clauses := !clauses @ new_clauses
  
let parse_meta_clauses str =
  Parser.meta_clauses Lexer.token (Lexing.from_string str)

let meta_clauses : meta_clause list ref =
  ref (parse_meta_clauses
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
  if not (List.mem_assoc name sequent.vars) then
    add_var (name, v)

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
    | _ -> "Variables: " ^ (String.concat ", " (List.map fst sequent.vars))

let format_hyp fmt (id, t) =
  fprintf fmt "%s : " id ;
  format_lppterm fmt t ;
  pp_force_newline fmt ()
    
let format_hyps fmt =
  List.iter (format_hyp fmt) sequent.hyps
   
let format_other_subgoals fmt =
  save_undo_state () ;
  let n = ref 1 in
    List.iter (fun set_state ->
                 set_state () ;
                 incr n ;
                 fprintf fmt "@[<1>subgoal %d is:@\n%a@]@\n@\n"
                   !n format_lppterm sequent.goal)
      !subgoals ;
    undo ()

let format_sequent fmt =
  pp_open_box fmt 2 ;
  fprintf fmt "  %s@\n" (vars_to_string ()) ;
  format_hyps fmt ;
  fprintf fmt "============================@\n" ;
  fprintf fmt " %a" format_lppterm sequent.goal ;
  pp_close_box fmt ()
      
let format_display fmt =
  pp_open_box fmt 0 ;
  fprintf fmt "%d subgoal(s).@\n@\n" (1 + List.length !subgoals) ;
  format_sequent fmt ;
  fprintf fmt "@\n@\n" ;
  format_other_subgoals fmt ;
  pp_close_box fmt () ;
  pp_print_flush fmt ()
    
let display () =
  format_display std_formatter

let get_display () =
  let b = Buffer.create 100 in
    format_display (formatter_of_buffer b) ;
    Buffer.contents b
    

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
    goal

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

let goal_to_subgoal g =
  let saved_sequent = copy_sequent () in
  let bind_state = Term.get_bind_state () in
    fun () ->
      set_sequent saved_sequent ;
      Term.set_bind_state bind_state ;
      sequent.goal <- g
      
let apply h args =
  save_undo_state () ;
  let stmt = get_hyp_or_lemma h in
  let args = List.map get_some_hyp args in
  let result, obligations = Tactics.apply stmt args in
  let remaining_obligations =
    List.remove_all (fun g -> search_goal (normalize g)) obligations in
  let obligation_subgoals = List.map goal_to_subgoal remaining_obligations in
  let resulting_subgoal =
    let restore = goal_to_subgoal sequent.goal in
      fun () ->
        restore () ;
        add_hyp (normalize result)
  in
    subgoals :=
      List.append obligation_subgoals (resulting_subgoal :: !subgoals );
    next_subgoal ()

    
(* Case analysis *)

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
  let term = get_hyp str in
  let cases =
    Tactics.case ~used:sequent.vars ~clauses:!clauses
      ~meta_clauses:!meta_clauses term
  in
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

let intros () =
  save_undo_state () ;
  let rec aux term =
    match term with
      | Binding(Forall, bindings, body) ->
          List.iter add_var
            (fresh_alist ~tag:Eigen ~used:sequent.vars bindings) ;
          aux (replace_lppterm_vars sequent.vars body)
      | Binding(Nabla, bindings, body) ->
          List.iter add_var
            (fresh_alist ~tag:Nominal ~used:sequent.vars bindings) ;
          aux (replace_lppterm_vars sequent.vars body)
      | Arrow(left, right) ->
          add_hyp left ;
          aux right
      | _ -> term
  in
    sequent.goal <- aux sequent.goal
            
let intro () =
  save_undo_state () ;
  match sequent.goal with
    | Binding(Forall, first::rest, body) ->
        let alist = fresh_alist ~tag:Eigen ~used:sequent.vars [first] in
          List.iter add_var alist ;
          let fresh_body = replace_lppterm_vars alist body in
            sequent.goal <- forall rest fresh_body
    | _ -> ()
            

(* Split *)

let split () =
  match sequent.goal with
    | And(left, right) ->
        subgoals := (goal_to_subgoal right) :: !subgoals ;
        sequent.goal <- left
    | _ -> ()


(* Exists *)

let exists t =
  match sequent.goal with
    | Binding(Lppterm.Exists, id::ids, body) ->
        let t = replace_term_vars sequent.vars t in
        let goal = exists ids (replace_lppterm_vars [(id, t)] body) in
          sequent.goal <- goal
    | _ -> ()
        
(* Skip *)

let skip () =
  save_undo_state () ;
  next_subgoal ()
