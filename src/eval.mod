eval (abs R) (abs R).

eval (app M N) V :- eval M (abs R), eval (R N) V.

typeof (abs R) (arrow T U) :- pi x\ (typeof x T => typeof (R x) U).

typeof (app M N) T :- typeof M (arrow U T), typeof N U.
