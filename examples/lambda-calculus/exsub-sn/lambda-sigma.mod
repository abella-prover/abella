module lambda-sigma.

accumulate sigma-strong.

ty base.
ty (arrow A B) :- ty A, ty B.

ctx empty.
ctx (cons G A) :- ctx G, ty A.

% Weak (syntactic) Sigma Normal Form
% Equivalent to snf on terms, but does not include eta on substitutions
wsnf (c A).
wsnf (var N).
wsnf (app M1 M2) :- wsnf M1, wsnf M2.
wsnf (lam M) :- wsnf M.
wssnf (shift N).
wssnf (dot M S) :- wsnf M, wssnf S.

convtm (c A) ec.
convtm (var N) (evar N).
convtm (clos M S) (eclos E1 E2) :- convtm M E1, convsub S E2.
convtm (app M1 M2) (edot E1 E2) :- convtm M1 E1, convtm M2 E2.
convtm (lam M) (elam E) :- convtm M E.
convsub (shift N) (eshift N).
convsub (dot M S) (edot E1 E2) :- convtm M E1, convsub S E2.
convsub (comp S1 S2) (eclos E1 E2) :- convsub S1 E1, convsub S2 E2.

step T (clos M S) (clos M' S) :- step T M M'.
step su (clos M S) (clos M S') :- steps su S S'.
step T (app M N) (app M' N) :- step T M M'.
step T (app M N) (app M N') :- step T N N'.
step T (lam M) (lam M') :- step T M M'.
steps T (dot M S) (dot M' S) :- step T M M'.
steps T (dot M S) (dot M S') :- steps T S S'.
step be (app (lam M) N) (clos M (dot N (shift z))).
step su (clos (c A) S) (c A).
step su (clos (var z) (dot M S)) M.
step su (clos (var (s N1)) (dot M S)) (clos (var N1) S).
step su (clos (var N1) (shift N2)) (var N3) :- add N1 N2 N3.
step su (clos (clos M S1) S2) (clos M (comp S1 S2)).
step su (clos (app M N) S) (app (clos M S) (clos N S)).
step su (clos (lam M) S) (lam (clos M (dot (var z) (comp S (shift (s z)))))).
steps su (dot (var K) (shift (s K))) (shift K).
steps T (comp S1 S2) (comp S1' S2) :- steps T S1 S1'.
steps T (comp S1 S2) (comp S1 S2') :- steps T S2 S2'.
steps su (comp (shift z) S) S.
steps su (comp (dot M S1) S2) (dot (clos M S2) (comp S1 S2)).
steps su (comp (shift (s N)) (dot M S)) (comp (shift N) S).
steps su (comp (shift N1) (shift N2)) (shift N3) :- add N1 N2 N3.
steps su (comp (comp S1 S2) S3) (comp S1 (comp S2 S3)).

tm (c A).
tm (var N) :- nat N.
tm (clos M S) :- tm M, sub S.
tm (app M1 M2) :- tm M1, tm M2.
tm (lam M) :- tm M.
sub (shift N) :- nat N.
sub (dot M S) :- tm M, sub S.
sub (comp S1 S2) :- sub S1, sub S2.

