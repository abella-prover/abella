open Lppterm

type id = string

type command =
  | Induction of int list
  | Apply of id * id list
  | Case of id
  | Search
  | Theorem of lppterm
  | Intros
