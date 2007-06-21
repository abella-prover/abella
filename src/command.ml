open Lppterm
open Term

type id = string

type top_command =
  | Theorem of id * lppterm

type command =
  | Induction of int
  | Apply of id * id list
  | Cut of id * id
  | Inst of id * term
  | Case of id
  | Search
  | Intros
  | Skip
  | Undo
