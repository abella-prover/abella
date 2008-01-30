type top.
type (arrow A B) :- type A, type B.

term (app M N) :- term M, term N.
term (abs A R) :- type A, pi x\ term x => term (R x).

value (abs A R).

typeof (app M N) B :- typeof M (arrow A B), typeof N A.
typeof (abs A R) (arrow A B) :- pi x\ (typeof x A => typeof (R x) B).

step (app M N) (app M' N) :- step M M'.
step (app M N) (app M N') :- value M, step N N'.
step (app (abs A R) M) (R M) :- value M.

nstep M M.
nstep M N :- step M P, nstep P N.
