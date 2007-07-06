wfe nil.
wfe (cons (pair X T) A) :- wf A T, wfe A.

wf A X :- var X, in_domain X A, wfe A.
wf A top :- wfe A.
wf A (arrow T1 T2) :- wf A T1, wf A T2.
wf A (all T1 T2) :- wf A T1, pi x\ var x => wf (cons (pair x T1) A) (T2 x).

in_domain X A :- member (pair X T) A.

member X (cons X A).
member X (cons Y A) :- member X A.

wfp A B :- perm A B, wfe A, wfe B.

perm nil nil.
perm A (cons X B') :- select A X A', perm A' B'.

select (cons X A) X A.
select (cons Y A) X (cons Y A') :- select A X A'.

append nil C C.
append (cons X A) B (cons X C) :- append A B C.

sub A S top.
sub A X X :- var X, wf A X.
sub A X T :- var X, member (pair X U) A, sub A U T.
sub A (arrow S1 S2) (arrow T1 T2) :- sub A T1 S1, sub A S2 T2.
sub A (all S1 S2) (all T1 T2) :-
    sub A T1 S1,
    pi x\ var x => sub (cons (pair x T1) A) (S2 x) (T2 x).
