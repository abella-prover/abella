open Term

type clause = term * term list
type clauses = clause list
let clauses : clauses ref = ref []
