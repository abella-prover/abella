module bred.

is_tm (lam M) :-
  pi x\ is_tm x => is_tm (M x).
is_tm (app M N) :-
  is_tm M, is_tm N.
is_tm (beta R N) :-
  (pi x\ is_tm x => is_tm (R x)),
  is_tm N.

is_p (left P) :- is_p P.
is_p (right P) :- is_p P.
is_p (bnd P) :-
  pi p\ is_p p => is_p (P p).
is_p done.

bred (lam M) (lam U) :-
  pi x\ bred x x => bred (M x) (U x).
bred (app M N) (app U V) :-
  bred M U, bred N V.
bred (beta R N) V :-
  pi x\ (pi u\ bred N u => bred x u)
    => bred (R x) V.

path (lam M) (bnd P) :-
  pi x\ pi p\ path x p => path (M x) (P p).
path (app M N) (left P) :-
  path M P.
path (app M N) (right P) :-
  path N P.
path (beta R N) P :-
  pi x\ 
    (pi q\ path N q => path x q) =>
    path (R x) P.
path M done.

bfree (lam M) :- pi x\ bfree x => bfree (M x).
bfree (app M N) :- bfree M, bfree N.
