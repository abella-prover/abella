open Term
open Typing

exception TranslationError of string

val translate : uterm -> term
