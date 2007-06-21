open Term

type clauses = (term * term list) list
let clauses : clauses ref = ref []
