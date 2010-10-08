module strong-ext.

accumulate strong-norm.

step1 C N T (clos M S) (clos M' S) :- step1 C N T M M'.
step1 clo z su (clos M S) (clos M S') :- step1s C z su S S'.
step1 clo (s N) T (clos M S) (clos M S') :- step1s C N T S S'.
step1 C N T (app M1 M2) (app M1' M2) :- step1 C N T M1 M1'.
step1 C N T (app M1 M2) (app M1 M2') :- step1 C N T M2 M2'.
step1 C N T (lam M) (lam M') :- step1 C N T M M'.
step1s C N T (dot M S) (dot M' S) :- step1 C N T M M'.
step1s C N T (dot M S) (dot M S') :- step1s C N T S S'.
step1 noc N be (app (lam M1) M2) (clos M1 (dot M2 (shift z))).
step1 noc N su (clos (c A) S) (c A).
step1 noc N su (clos (var z) (dot M S)) M.
step1 noc N su (clos (var (s N1)) (dot M S)) (clos (var N1) S).
step1 noc N su (clos (var N1) (shift N2)) (var N3) :- add N1 N2 N3.
step1 noc N su (clos (clos M S1) S2) (clos M (comp S1 S2)).
step1 noc N su (clos (app M1 M2) S) (app (clos M1 S) (clos M2 S)).
step1 noc N su (clos (lam M) S) (lam (clos M (dot (var z) (comp S (shift (s z)))))).
step1s noc N su (dot (var K) (shift (s K))) (shift K).
step1s C N T (comp S1 S2) (comp S1' S2) :- step1s C N T S1 S1'.
step1s C N T (comp S1 S2) (comp S1 S2') :- step1s C N T S2 S2'.
step1s noc N su (comp (shift z) S) S.
step1s noc N su (comp (dot M S1) S2) (dot (clos M S2) (comp S1 S2)).
step1s noc N su (comp (shift (s N1)) (dot M S)) (comp (shift N1) S).
step1s noc N su (comp (shift N1) (shift N2)) (shift N3) :- add N1 N2 N3.
step1s noc N su (comp (comp S1 S2) S3) (comp S1 (comp S2 S3)).

mstep1_clo N M M.
mstep1_clo N M1 M3 :- step1 clo N T M1 M2, mstep1_clo N M2 M3.
mstep1s_clo N S S.
mstep1s_clo N S1 S3 :- step1s clo N T S1 S2, mstep1s_clo N S2 S3.

mstep1 N M M.
mstep1 N M1 M3 :- step1 C N T M1 M2, mstep1 N M2 M3.
mstep1s N S S.
mstep1s N S1 S3 :- step1s C N T S1 S2, mstep1s N S2 S3.

wcomp N1 (shift N2) (shift N3) :- add N1 N2 N3.
wcomp z (dot M S) (dot M S).
wcomp (s N) (dot M S1) S2 :- wcomp N S1 S2.
wcomp N1 (comp S1 S2) S :- wcomp N1 S1 (shift N2), wcomp N2 S2 S.
wcomp N1 (comp S1 S2) (dot (clos M S2) (comp S S2)) :- wcomp N1 S1 (dot M S).

