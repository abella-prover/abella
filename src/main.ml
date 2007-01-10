open Prover
open Pprint
open Lppterm

let rec process_proof ?(interactive=true) lexbuf =
  try while true do try
    display () ;
    if interactive then Format.printf "Proof < %!" ;
    begin match Parser.command Lexer.token lexbuf with
      | Induction(args) -> induction args
      | Apply(h, args) -> apply h args
      | Case(str) -> case str
      | Search -> search ()
      | Intros -> intros ()
    end ;
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

let rec process ?(interactive=true) lexbuf =
  try while true do try
    if interactive then Format.printf "LPP < %!" ;
    begin match Top_parser.top_command Top_lexer.token lexbuf with
      | Theorem(thm) ->
          theorem thm ;
          process_proof ~interactive:interactive lexbuf
    end ;
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
  Pprint.set_infix [("=>", Pprint.Right)] ;
  process ~interactive:true (Lexing.from_channel stdin)











