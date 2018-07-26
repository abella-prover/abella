module pclf.

ty top.
ty nat.
ty (list T) :- ty T.
ty (arr S T) :- ty S, ty T.

of zero nat.
of (succ M) nat :- of M nat.
of (app M N) T :- ty S, of M (arr S T), of N S.
of (lam R) (arr S T) :- pi x\ of x S => of (R x) T.
of (fix R) T :- pi x\ of x T => of (R x) T.
of unit top.
of nill (list T).
of (cons M N) (list T) :- of M T, of N (list T).
of (lcase M N R) T :- ty S, of M (list S), of N T,
  pi h\ of h S => pi k\ of k (list S) => of (R h k) T.
of (ncase M N R) T :- of M nat, of N T,
  pi x\ of x nat => of (R x) T.

cp zero zero.
cp (succ M) (succ SM) :-
  cp M SM.
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
cp (ncase M N R) (ncase SM SN SR) :-
  cp M SM, cp N SN,
  pi x\ cp x x => cp (R x) (SR x).

eval V V :- value V.
eval (fix R) V :-
  eval (R (fix R)) V.
eval (app M N) V :-
  eval M (lam R), eval (R N) V.
eval (lcase M N R) V :-
  eval M nill, eval N V.
eval (lcase M N R) V :-
  eval M (cons H K), eval (R H K) V.
eval (ncase M N R) V :-
  eval M zero, eval N V.
eval (ncase M N R) V :-
  eval M (succ K), eval (R K) V.

value zero.
value (succ M).
value nill.
value (cons M N).
value (lam R).