open Term
open Lppterm

type id = string
    
type vars = (id * term) list
type hyps = (id * lppterm) list

let freshHyp =
  let count = ref 0 in
    fun () ->
      incr count ;
      "H" ^ (string_of_int !count)

type clauses = (lppterm * lppterm list) list
