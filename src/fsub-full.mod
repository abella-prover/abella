sub G S top.

sub G (var X) (var X).

sub G (var X) T :- bound X U G, sub G U T.

sub G (arrow S1 S2) (arrow T1 T2) :- sub G T1 S1, sub G S2 T2.

sub G (forall S1 (x\ S2 x)) (forall T1 (x\ T2 x)) :-
    sub G T1 S1,
    pi x\ sub (cons x T1 G) (S2 x) (T2 x).

bound X T (cons X T G).
bound X T (cons Y S G) :- bound X T G.

subsumes nil nil.
subsumes (cons X T G1) (cons X T G2) :- subsumes G1 G2.
subsumes (cons X Q G) (cons X P G) :- sub G P Q.
