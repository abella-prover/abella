% and is a reserved work so we'll use land
conc A :- hyp A.
conc top.

conc (land A B) :- conc A, conc B.
conc C :- hyp (land A B), hyp A => hyp B => conc C.

conc (imp A B) :- hyp A => conc B.
conc C :- hyp (imp A B), conc A, hyp B => conc C.

prop top.
prop (land A B) :- prop A, prop B.
prop (imp A B) :- prop A, prop B.
