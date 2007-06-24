open Lppterm
open Term
open Printf

type clause = term * term list
type clauses = clause list

type id = string

type top_command =
  | Theorem of id * lppterm
  | Axiom of id * lppterm
  | Def of clause

type command =
  | Induction of int
  | Apply of id * id list
  | Cut of id * id
  | Inst of id * term
  | Case of id
  | Assert of lppterm
  | Search
  | Intros
  | Skip
  | Undo

let clause_to_string (head, body) =
  sprintf "%s :- %s"
    (term_to_string head)
    (String.concat ", " (List.map term_to_string body))

let top_command_to_string tc =
  match tc with
    | Theorem(name, body) ->
        sprintf "Theorem %s : %s" name (lppterm_to_string body)
    | Axiom(name, body) ->
        sprintf "Axiom %s : %s" name (lppterm_to_string body)
    | Def clause ->
        sprintf "Def %s" (clause_to_string clause)

let command_to_string c =
  match c with
    | Induction i ->
        sprintf "induction on %d" i
    | Apply(h, hs) ->
        sprintf "apply %s to %s" h (String.concat " " hs)
    | Cut(h1, h2) ->
        sprintf "cut %s with %s" h1 h2
    | Inst(h, t) ->
        sprintf "inst %s with %s" h (term_to_string t)
    | Case h ->
        sprintf "case on %s" h
    | Assert t ->
        sprintf "assert %s" (lppterm_to_string t)
    | Search -> "search"
    | Intros -> "intros"
    | Skip -> "skip"
    | Undo -> "undo"
      
