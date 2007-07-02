copy (app N M) (app P Q) :- copy N P, copy M Q.
copy (abs R) (abs S) :- pi x\ pi y\ copy x y => copy (R x) (S y).

copy' (app N M) (app P Q) :- copy' N P, copy' M Q.
copy' (abs R) (abs S) :- pi x\ pi y\ copy' x y => copy' (R x) (S y).

copy'' (app N M) (app P Q) :- copy'' N P, copy'' M Q.
copy'' (abs R) (abs S) :- pi x\ copy' x x => copy' (R x) (S x).
