typeof (abs T R) (arrow T U) :- pi x\ (typeof x T => typeof (R x) U).
typeof (app M N) T :- typeof M (arrow U T), typeof N U.
