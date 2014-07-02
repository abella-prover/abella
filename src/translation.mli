open Term

exception TranslationError of string

val trans_type : Uterm.uterm -> Term.ty

val translate : Uterm.uterm -> term

val lfobj_to_string : Metaterm.obj -> string
