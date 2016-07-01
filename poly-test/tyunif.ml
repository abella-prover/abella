open Typing;;
open Term;;

let a = tybase (atybase "A") in
let b = tybase (atybase "B") in
let tylst1 = tybase (AtmTy ("list", [a])) in
let tylst2 = tybase (AtmTy ("list", [b])) in
let info = (ghost, CArg) in
let c = (tylst1, tylst2, info) in
let gen_vars = ["A";"B"] in
unify_constraints ~gen_vars [c]
