open Prover
open Lppterm
open Types
open Printf

let rec process_proof name ~interactive lexbuf =
  let finished = ref false in
    try while not !finished do try
      display () ;
      printf "%s < %!" name ;
      let input = Parser.command Lexer.token lexbuf in
        if not interactive then printf "%s.\n\n" (command_to_string input) ;
        begin match input with
          | Induction(args) -> induction args
          | Apply(h, args) -> apply h args
          | Cut(h, arg) -> cut h arg
          | Inst(h, t) -> inst h t
          | Case(str) -> case str
          | Assert(t) -> assert_hyp t
          | Search -> search ()
          | Intros -> intros ()
          | Skip -> skip ()
          | Undo -> undo ()
        end ;
        if interactive then flush stdout
    with
      | Failure "lexing: empty token" ->
          exit (if interactive then 0 else 1)
      | Failure "Proof completed." ->
          print_endline "Proof completed." ;
          reset_prover () ;
          finished := true
      | Failure s ->
          printf "Error: %s\n" s ;
          if not interactive then exit 1
      | End_of_file ->
          print_endline "Proof NOT completed." ;
          exit 1
      | e ->
          printf "Unknown error: %s\n%!" (Printexc.to_string e) ;
          if not interactive then exit 1
    done with
      | Failure "eof" -> ()

let rec process ~interactive lexbuf =
  try while true do try
    printf "LPP < %!" ;
    let input = Parser.top_command Lexer.token lexbuf in
      if not interactive then printf "%s.\n\n" (top_command_to_string input) ;
      begin match input with
        | Theorem(name, thm) ->
            theorem thm ;
            process_proof ~interactive:interactive name lexbuf ;
            add_lemma name thm
        | Axiom(name, axiom) ->
            add_lemma name axiom
        | Def(clause) ->
            add_meta_clause clause
      end ;
      if interactive then flush stdout
  with
    | Failure "lexing: empty token" ->
        exit (if interactive then 0 else 1)
    | Failure s ->
        printf "Error: %s\n" s ;
        if not interactive then exit 1
    | End_of_file ->
        print_endline "Goodbye." ;
        exit 0
    | e ->
        printf "Unknown error: %s\n%!" (Printexc.to_string e)
  done with
  | Failure "eof" -> ()

let welcome_msg = "Lambda Prolog Prover 0.1\n"

let usage_message = ""

let command_input = ref ""

let _ =
  printf "%s%!" welcome_msg ;
  Arg.parse
    [("-f", Arg.Set_string command_input, "Read command input from file")]
    (fun file_name ->
       Printf.printf "Reading clauses from %s\n" file_name ;
       add_clauses (Parser.clauses Lexer.token
                      (Lexing.from_channel (open_in file_name))))
    usage_message ;
  if !command_input = "" then
    process ~interactive:true (Lexing.from_channel stdin)
  else
    process ~interactive:false (Lexing.from_channel (open_in !command_input))
        
