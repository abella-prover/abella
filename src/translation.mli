open Term

exception TranslationError of string

val trans_type : Uterm.uterm -> Term.ty

val translate : ?used:(id * term) list -> sign:(id * ty) list -> Uterm.uterm -> term

val elf_printer : term_printer

val lfterm_to_string : Term.term -> Term.tyctx -> int -> string
