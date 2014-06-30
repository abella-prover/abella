open Term
(* open Typing *)

exception TranslationError of string

val translate : Uterm.uterm -> term

val lfobj_to_string : Metaterm.obj -> string
