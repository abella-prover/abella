module poplmark-1a.

sub S top.

sub X X :- bound X U.

sub X T :- bound X U, sub U T.

sub (arrow S1 S2) (arrow T1 T2) :- sub T1 S1, sub S2 T2.

sub (all S1 (x\ S2 x)) (all T1 (x\ T2 x)) :-
    sub T1 S1,
    pi x\ (bound x T1 => sub (S2 x) (T2 x)).
