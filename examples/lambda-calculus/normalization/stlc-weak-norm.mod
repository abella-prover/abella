module stlc-weak-norm.

value (abs A R).

of (app M N) B :- of M (arrow A B), of N A.
of (abs A R) (arrow A B) :- pi x\ of x A => of (R x) B.

step (app M N) (app M' N) :- step M M'.
step (app M N) (app M N') :- value M, step N N'.
step (app (abs A R) M) (R M) :- value M.

steps M M.
steps M N :- step M P, steps P N.
