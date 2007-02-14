typeof (abs R) (arrow T U) :- pi x\ (typeof x T => typeof (R x) U).
typeof (app M N) T :- typeof M (arrow U T), typeof N U.

eval (abs R) (abs R).
eval (app M N) V :- eval M (abs R), eval (R N) V.

step (app (abs R) M) (R M).
step (app M N) (app M' N) :- step M M'.

nstep A A.
nstep A C :- step A B, nstep B C.

eq X X.
