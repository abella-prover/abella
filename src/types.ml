open Lppterm
open Term

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
