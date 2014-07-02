open Term

exception TranslationError of string

val trans_type : Uterm.uterm -> Term.ty

val translate : Uterm.uterm -> term

val lfterm_to_string : Term.term -> Term.id list -> int -> string
