eval zero zero.
eval true true.
eval false false.
eval (succ M) (succ V) :- eval M V.
eval (pred M) zero :- eval M zero.
eval (pred M) V :- eval M (succ V).
eval (is_zero M) true :- eval M zero.
eval (is_zero M) false :- eval M (succ V).
eval (if M N1 N2) V :- eval M true, eval N1 V.
eval (if M N1 N2) V :- eval M false, eval N2 V.
eval (abs T R) (abs T R).
eval (app M N) V :- eval M (abs T R), eval (R N) V.
eval (rec T R) V :- eval (R (rec T R)) V.

typeof zero num.
typeof true bool.
typeof false bool.
typeof (succ M) num :- typeof M num.
typeof (pred M) num :- typeof M num.
typeof (is_zero M) bool :- typeof M num.
typeof (if M N1 N2) T :- typeof M bool, typeof N1 T, typeof N2 T.
typeof (abs T R) (arr T U) :- pi n\ (typeof n T => typeof (R n) U).
typeof (app M N) T :- typeof M (arr U T), typeof N U.
typeof (rec T R) T :- pi n\ (typeof n T => typeof (R n) T).
