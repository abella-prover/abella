open Term

type clause = term * term list
type clauses = clause list
let clauses : clauses ref = ref [(binop "=" (const "X") (const "X"), [])]

let reset =
  let original_clauses = !clauses in
    fun () -> clauses := original_clauses

let add_clauses new_clauses =
  clauses := new_clauses @ !clauses

  
