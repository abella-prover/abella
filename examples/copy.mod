module copy.

copy (app N M) (app P Q) :- copy N P, copy M Q.
copy (abs R) (abs S) :- pi x\ copy x x => copy (R x) (S x).

copy2 (app N M) (app P Q) :- copy2 N P, copy2 M Q.
copy2 (abs R) (abs S) :- pi x\ pi y\ copy2 x y => copy2 (R x) (S y).
