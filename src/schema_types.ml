open Metaterm
open Term
open Typing
open Printf

type id = string

(* type definition *)
type top_command = 
  | SchemaDef of id * (id list * id list * (uterm option) list) list

type command = 
  | Inversion of id list
  | Projection of id list * id list
  | Unique of id list
  | Sync of id list
