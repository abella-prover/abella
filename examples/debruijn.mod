module debruijn.

add z C C.
add (s A) B (s C) :- add A B C.

% H here is the height (depth) of lambda abstractions
ho2db (app M N) H (dapp DM DN) :- ho2db M H DM, ho2db N H DN.
ho2db (lam R) H (dlam DR) :- pi x\ store x H => ho2db (R x) (s H) DR.
ho2db X H (dvar DX) :- store X HX, add HX DX H.

beta (app (lam R) M) (R M).

eta (app M N) (app M' N) :- eta M M'.
eta (app M N) (app M N') :- eta N N'.
eta (lam R) (lam R) :- pi x\ eta (R x) (R' x).
eta (lam x\ (app R x)) R.

deta (dapp M N) (dapp M' N) :- deta M M'.
deta (dapp M N) (dapp M N') :- deta N N'.
deta (dlam R) (dlam R) :- deta R R'.
deta (dlam (dapp R (dvar (s z)))) R :- free (s z) R.

free X (dapp M N) :- free X M, free X N.
free X (dlam R) :- free (s X) R.
free X (dvar Y) :- neq X Y.

neq (s X) z.
neq z (s Y).
neq (s X) (s Y) :- neq X Y.
