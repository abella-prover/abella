open Term
open Pprint
open Lppterm
open Command

type id = string
    
type vars = (id * term) list
type hyps = (id * lppterm) list

type state = vars * hyps * lppterm
    
let freshHyp =
  let count = ref 0 in
    fun () ->
      incr count ;
      "H" ^ (string_of_int !count)

let parse_command str =
  Parser.command Lexer.token (Lexing.from_string str)

let vars_to_string vars =
  String.concat "\n"
    (List.map (fun (id, t) -> "  " ^ id ^ " : " ^ (term_to_string t)) vars)

let hyps_to_string hyps =
  String.concat "\n"
    (List.map (fun (id, t) -> "  " ^ id ^ " : " ^ (lppterm_to_string t)) hyps)
   
let div = "  ============================\n"
  
let display (vars, hyps, goal) =
  print_string (vars_to_string vars) ;
  print_string (hyps_to_string hyps) ;
  print_string div ;
  print_string (lppterm_to_string goal )
    
