copy (app N M) (app P Q) :- copy N P, copy M Q.
copy (abs R) (abs S) :- pi x\ pi y\ copy x y => copy (R x) (S y).

subst R T S :- pi x\ copy x T => copy (R x) S.
