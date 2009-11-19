module debruijn.

add z C C.
add (s A) B (s C) :- add A B C.

% H here is the height (depth) of lambda abstractions
ho2db (app M N) H (dapp DM DN) :- ho2db M H DM, ho2db N H DN.
ho2db (lam R) H (dlam DR) :- pi x\ depth x H => ho2db (R x) (s H) DR.
ho2db X H (dvar DX) :- depth X HX, add HX DX H.
