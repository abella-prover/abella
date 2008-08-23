% The actual structure of propositions does not matter, but
% we use this predicate as a measure for induction.
prop top.
prop (p X).                             % an arbitrary unary predicate P
prop (and A B) :- prop A, prop B.
prop (or A B) :- prop A, prop B.
prop (imp A B) :- prop A, prop B.
prop (all A) :- pi x\ prop (A x).


conc A :- hyp A.
conc top.

conc (and A B) :- conc A, conc B.
conc C :- hyp (and A B), hyp A => hyp B => conc C.

conc (or A B) :- conc A.
conc (or A B) :- conc B.
conc C :- hyp (or A B), hyp A => conc C, hyp B => conc C.

conc (imp A B) :- hyp A => conc B.
conc C :- hyp (imp A B), conc A, hyp B => conc C.

conc (all A) :- pi x\ conc (A x).
conc C :- hyp (all A), hyp (A T) => conc C.
