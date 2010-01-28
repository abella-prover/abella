module stlc-strong-norm.

ty top.
ty (arrow A B) :- ty A, ty B.

of (app M N) B :- of M (arrow A B), of N A.
of (abs A R) (arrow A B) :- ty A, pi x\ (of x A => of (R x) B).

% We add this since Girard's proof assumes we can always find
% at least one element in the reducability relation
of c A :- ty A.

step (app M N) (app M' N) :- step M M'.
step (app M N) (app M N') :- step N N'.
step (app (abs A R) M) (R M).
step (abs A R) (abs A R') :- pi x\ step (R x) (R' x).
