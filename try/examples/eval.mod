module eval.

of (abs R) (arrow T U) :- pi x\ (of x T => of (R x) U).
of (app M N) T :- of M (arrow U T), of N U.

eval (abs R) (abs R).
eval (app M N) V :- eval M (abs R), eval (R N) V.

step (app (abs R) M) (R M).
step (app M N) (app M' N) :- step M M'.

nstep A A.
nstep A C :- step A B, nstep B C.
