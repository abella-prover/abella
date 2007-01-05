type 'a t

exception Cannot_table

val empty  : 'a t
val find   : 'a t -> Term.term list -> 'a option
val add    : ?allow_eigenvar:bool -> 'a t -> Term.term list -> 'a -> 'a t
val iter   : 'a t -> (Term.term -> 'a -> unit) -> unit
