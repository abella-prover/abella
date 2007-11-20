eval (fun A F) (fun A F).
eval (app T1 T2) V :- eval T1 (fun A F),
                      eval T2 V2,
                      eval (F V2) V.

typeof (fun A F) (arrow A B) :-
    pi x\ typeof x A => typeof (F x) B.

typeof (app T1 T2) B :- typeof T1 (arrow A B),
                        typeof T2 A.
