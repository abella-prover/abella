module pclf.

ty top.
ty (list T) :- ty T.
ty (arr S T) :- ty S, ty T.

of (app M N) T :- of M (arr S T), of N S.
of (lam R) (arr S T) :- pi x\ of x S => of (R x) T.
of (fix R) T :- pi x\ of x T => of (R x) T.
of unit top.
of nill (list T).
of (cons M N) (list T) :- of M T, of N (list T).
of (lcase M N R) T :- of M (list S), of N T,
  pi h\ of h S => pi k\ of k (list S) => of (R h k) T.

cp (app M N) (app SM SN) :-
  cp M SM, cp N SN.
cp (lam R) (lam SR) :-
  pi x\ cp x x => cp (R x) (SR x).
cp (fix R) (fix SR) :-
  pi x\ cp x x => cp (R x) (SR x).
cp unit unit.
cp nill nill.
cp (cons M N) (cons SM SN) :-
  cp M SM, cp N SN.
cp (lcase M N R) (lcase SM SN SR) :-
  cp M SM, cp N SN,
  pi h\ cp h h => pi k\ cp k k => cp (R h k) (SR h k).