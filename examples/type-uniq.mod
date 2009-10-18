module type-uniq.

of (abs T R) (arrow T U) :- pi x\ (of x T => of (R x) U).
of (app M N) T :- of M (arrow U T), of N U.
