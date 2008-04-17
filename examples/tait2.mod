type top.
type (arrow A B) :- type A, type B.

value (abs A R).

of (app M N) B :- of M (arrow A B), of N A.
of (abs A R) (arrow A B) :- type A, pi x\ (of x A => of (R x) B).
% We add [type A] in order to reflect typing during reasoning.
% Without this we would have to worry about judgments like
%   of (abs bad (x\ x)) (arrow bad bad)
% which doesn't make sense since bad isn't a valid type.

step (app M N) (app M' N) :- step M M'.
step (app M N) (app M N') :- value M, step N N'.
step (app (abs A R) M) (R M) :- value M.

nstep M M.
nstep M N :- step M P, nstep P N.
