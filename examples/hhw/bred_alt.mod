module bred_alt.

bred (abs M) (abs U) :-
  pi x\ bred x x => bred (M x) (U x).
bred (app M N) (app U V) :-
  bred M U, bred N V.
bred (beta R N) V :- bred (R N) V.

path (abs M) (bnd P) :-
  pi x\ pi p\ path x p => path (M x) (P p).
path (app M N) (left P) :-
  path M P.
path (app M N) (right P) :-
  path N P.
path (beta R N) P :-
  pi x\
    (pi q\ path N q => path x q) =>
    path (R x) P.

bfree (abs M) :- pi x\ bfree x => bfree (M x).
bfree (app M N) :- bfree M, bfree N.

tm (abs M) :- pi x\ tm x => tm (M x).
tm (app M N) :- tm M, tm N.
tm (beta R N) :- tm N, pi x\ tm x => tm (R x).