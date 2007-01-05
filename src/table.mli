type tag = Proved | Working of bool ref | Disproved | Unset
type t
    
val create : unit -> t

val add : allow_eigenvar:bool -> t -> Term.term list -> tag ref -> unit

val find : t -> Term.term list -> tag ref option

val print : string -> t -> unit

val reset : t -> unit
