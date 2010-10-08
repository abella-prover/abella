module sigma-strong.

accumulate add.

estep (eclos S1 S2) (eclos S1' S2) :- estep S1 S1'.
estep (eclos S1 S2) (eclos S1 S2') :- estep S2 S2'.
estep (edot S1 S2) (edot S1' S2) :- estep S1 S1'.
estep (edot S1 S2) (edot S1 S2') :- estep S2 S2'.
estep (elam S) (elam S') :- estep S S'.
estep (eclos ec S) ec.
estep (eclos (evar z) (edot M S)) M.
estep (eclos (evar (s N1)) (edot M S)) (eclos (evar N1) S).
estep (eclos (evar N1) (eshift N2)) (evar N3) :- add N1 N2 N3.
estep (eclos (eclos M S1) S2) (eclos M (eclos S1 S2)).
estep (eclos (edot M N) S) (edot (eclos M S) (eclos N S)).
estep (eclos (elam M) S) (elam (eclos M (edot (evar z) (eclos S (eshift (s z)))))).
estep (edot (evar K) (eshift (s K))) (eshift K).
estep (eclos (eshift z) S) S.
estep (eclos (eshift (s N)) (edot M S)) (eclos (eshift N) S).
estep (eclos (eshift N1) (eshift N2)) (eshift N3) :- add N1 N2 N3.

exp ec.
exp (evar N) :- nat N.
exp (eclos M S) :- exp M, exp S.
exp (edot M1 M2) :- exp M1, exp M2.
exp (elam M) :- exp M.
exp (eshift N) :- nat N.

subexp S S.
subexp S (eclos S1 S2) :- subexp S S1.
subexp S (eclos S1 S2) :- subexp S S2.
subexp S (edot S1 S2) :- subexp S S1.
subexp S (edot S1 S2) :- subexp S S2.
subexp S (elam S1) :- subexp S S1.


