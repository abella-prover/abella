open Typing
open Term
let ity = tybase "int" in
let ut1 = ULam (ghost, "x", ity, ULam (ghost, "y", ity, UCon (ghost, "x", ity))) in
let ut2 = ULam (ghost, "x", ity, ULam (ghost, "y", ity, UCon (ghost, "y", ity))) in
()
