module breduce_bv.

breduce (lam M) (lam U) :-
  pi x\ breduce x x => breduce (M x) (U x).
breduce (app M N) (app U V) :-
  breduce M U, breduce N V.
breduce (beta R N) V :-
  pi x\ breduce N x => breduce (R x) V.

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
