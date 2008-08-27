tm (app M N) :- tm M, tm N.
tm (abs R) :- pi x\ tm x => tm (R x).

path (app M N) (fst P) :- path M P.
path (app M N) (snd P) :- path N P.
path (abs R) (bnd S) :- pi x\ path x x => path (R x) (S x).
path M done. % we allow partial paths
