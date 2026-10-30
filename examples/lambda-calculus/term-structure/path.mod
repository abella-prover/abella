module path.

tm (app M N) :- tm M, tm N.
tm (abs R) :- pi x\ tm x => tm (R x).

path (app M N) (left P) :- path M P.
path (app M N) (right P) :- path N P.
path (abs R) (bnd S) :- pi x\ pi p\ path x p => path (R x) (S p).

