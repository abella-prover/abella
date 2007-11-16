eval (abs R) (abs R).
eval (app M N) V :- eval M (abs R), eval (R N) V.

pe (abs R) (abs R).
pe (app M N) V :- pe M (abs R), pe (R N) V.
pe (abs R) (abs R') :- pi x\ pi y\ pe x y => pe (R x) (R' y).
pe (app M N) (app M' N') :- pe M M', pe N N'.

