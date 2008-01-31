type top.
type (arrow A B) :- type A, type B.

term (app M N) :- term M, term N.
term (abs A R) :- type A, pi x\ term x => term (R x).

value (abs A R).

of (app M N) B :- of M (arrow A B), of N A.
of (abs A R) (arrow A B) :- type (arrow A B), pi x\ (of x A => of (R x) B).
% We add the type judgment in order to reflect typing during reasoning

step (app M N) (app M' N) :- step M M'.
step (app M N) (app M N') :- value M, step N N'.
step (app (abs A R) M) (R M) :- value M.

nstep M M.
nstep M N :- step M P, nstep P N.
