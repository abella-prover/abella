open Prover
open Lppterm
open Command
open Clauses

let rec process_proof name ?(interactive=true) lexbuf =
  let finished = ref false in
    try while not !finished do try
      display () ;
      if interactive then Format.printf "%s < %!" name ;
      begin match Parser.command Lexer.token lexbuf with
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
          Format.printf "Error: %s\n" s
      | End_of_file ->
          print_endline "Proof NOT completed." ;
          exit 1
      | e ->
          Format.printf "Unknown error: %s\n%!" (Printexc.to_string e)
    done with
      | Failure "eof" -> ()

let rec process ?(interactive=true) lexbuf =
  try while true do try
    if interactive then Format.printf "LPP < %!" ;
    begin match Parser.top_command Lexer.token lexbuf with
      | Theorem(name, thm) ->
          theorem thm ;
          process_proof ~interactive:interactive name lexbuf ;
          add_lemma name thm
      | Axiom(name, axiom) ->
          add_lemma name axiom
    end ;
    if interactive then flush stdout
  with
    | Failure "lexing: empty token" ->
        exit (if interactive then 0 else 1)
    | Failure s ->
        Format.printf "Error: %s\n" s
    | End_of_file ->
        print_endline "Goodbye." ;
        exit 0
    | e ->
        Format.printf "Unknown error: %s\n%!" (Printexc.to_string e)
  done with
  | Failure "eof" -> ()

let welcome_msg = "Lambda Prolog Prover 0.1\n"

let usage_message = ""
  
let _ =
  Format.printf "%s%!" welcome_msg ;
  Arg.parse []
    (fun file_name ->
       Printf.printf "Reading clauses from %s\n" file_name ;
       clauses :=
         List.append (Parser.clauses Lexer.token
                        (Lexing.from_channel (open_in file_name)))
           !clauses)
    usage_message ;
  process ~interactive:true (Lexing.from_channel stdin)
