sub G S top.
sub G (var X) (var X).
sub G (var X) T :- bound X U G, sub G U T.
sub G (arrow S1 S2) (arrow T1 T2) :- sub G T1 S1, sub G S2 T2.
sub G (forall S1 (x\ S2 x)) (forall T1 (x\ T2 x)) :-
    sub G T1 S1,
    pi x\ sub (cons x T1 G) (S2 x) (T2 x).

bound X T (cons (pair X T) G).
bound X T (cons P G) :- bound X T G.

indomain X G :- bound X T G.

wfe nil.
wfe (cons (pair X T) G) :- wf G T, wfe G.

wf G X :- isvar X, bound X T G, wfe G.
wf G top :- wfe G.
wf G (arrow T1 T2) :- wf G T1, wf G T2.
wf G (forall T1 (x\ T2 x)) :-
    wf G T1,
    pi x\ isvar x => wf (cons (pair x T1) G) (T2 x).

perm nil nil.
perm A (cons X B) :- select A X A', perm A' B.

select (cons X A) X A.
select (cons Y A) X (cons Y B) :- select A X B.

append nil B B.
append (cons X A) B (cons X C) :- append A B C.
