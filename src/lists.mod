append nil C C.
append (cons X A) B (cons X C) :- append A B C.

rev nil nil.
rev (cons X A) B :- rev A A', append A' (cons X nil) B.

eq X X.

select (cons X A) X A.
select (cons Y A) X (cons Y B) :- select A X B.

perm nil nil.
perm (cons X A') B :- perm A' B', select B X B'.
% Proofs don't yet work if select is first
