open Lppterm
open Term
open Printf

type clause = term * term list
type clauses = clause list

type meta_clause = term * lppterm list
type meta_clauses = meta_clause list

type id = string

type top_command =
  | Theorem of id * lppterm
  | Axiom of id * lppterm
  | Def of meta_clause

type command =
  | Induction of int
  | Apply of id * id list
  | Cut of id * id
  | Inst of id * id * term
  | Case of id
  | Assert of lppterm
  | Exists of term
  | Search
  | Split
  | Intros
  | Intro
  | Skip
  | Undo

let meta_clause_to_string (head, body) =
  if body = [] then
    term_to_string head
  else
    sprintf "%s :- %s"
      (term_to_string head)
      (String.concat ", " (List.map lppterm_to_string body))

let top_command_to_string tc =
  match tc with
    | Theorem(name, body) ->
        sprintf "Theorem %s : %s" name (lppterm_to_string body)
    | Axiom(name, body) ->
        sprintf "Axiom %s : %s" name (lppterm_to_string body)
    | Def clause ->
        sprintf "Def %s" (meta_clause_to_string clause)

let command_to_string c =
  match c with
    | Induction i ->
        sprintf "induction on %d" i
    | Apply(h, hs) ->
        sprintf "apply %s to %s" h (String.concat " " hs)
    | Cut(h1, h2) ->
        sprintf "cut %s with %s" h1 h2
    | Inst(h, n, t) ->
        sprintf "inst %s with %s = %s" h n (term_to_string t)
    | Case h ->
        sprintf "case %s" h
    | Assert t ->
        sprintf "assert %s" (lppterm_to_string t)
    | Exists t ->
        sprintf "exists %s" (term_to_string t)
    | Search -> "search"
    | Split -> "split"
    | Intros -> "intros"
    | Intro -> "intro"
    | Skip -> "skip"
    | Undo -> "undo"
      
