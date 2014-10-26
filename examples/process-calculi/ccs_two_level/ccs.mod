module ccs.

comp A (bar A).
comp (bar A) A.

step (out A P) A P.
step (plus P Q) A P1 :- step P A P1.
step (plus P Q) A Q1 :- step Q A Q1.
step (par P Q) A (par P1 Q) :- step P A P1.
step (par P Q) A (par P Q1) :- step Q A Q1.
step (mu P) A Q :- step (P (mu P)) A Q.
step (par P Q) tau (par P1 Q1) :- comp A B, step P A P1, step Q A Q1.
