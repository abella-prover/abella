prop top.
prop (and A B) :- prop A, prop B.
prop (imp A B) :- prop A, prop B.


conc A :- hyp A.
conc top.

conc (and A B) :- conc A, conc B.
conc C :- hyp (and A B), hyp A => hyp B => conc C.

conc (imp A B) :- hyp A => conc B.
conc C :- hyp (imp A B), conc A, hyp B => conc C.
