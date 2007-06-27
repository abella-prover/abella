copy (app N M) (app P Q) :- copy N P, copy M Q.
copy (abs R) (abs S) :- pi x\ copy x x => copy (R x) (S x).

subst R T S :- pi x\ copy x T => copy (R x) S.
