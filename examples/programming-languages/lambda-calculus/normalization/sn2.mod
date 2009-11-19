module sn2.

ty top.
ty (arrow A B) :- ty A, ty B.

of (app M N) B :- of M (arrow A B), of N A.
of (abs A R) (arrow A B) :- ty A, pi x\ (of x A => of (R x) B).
% We add [ty A] in order to reflect typing during reasoning.
% Without this we would have to worry about judgments like
%   of (abs bad (x\ x)) (arrow bad bad)
% which doesn't make sense since bad isn't a valid type.

step (app M N) (app M' N) :- step M M'.
step (app M N) (app M N') :- step N N'.
step (app (abs A R) M) (R M).
step (abs A R) (abs A R') :- pi x\ step (R x) (R' x).

% copying a term to another term.
% use this clause to define substitutions.
cp (app M N) (app M' N') :- cp M M', cp N N'.
cp (abs A M) (abs A R)   :- ty A, pi x\ pi y\ (cp x y => cp (M x) (R y)).
