list nil.
list (cons X L) :- list L.

append nil C C.
append (cons X A) B (cons X C) :- append A B C.

rev nil nil.
rev (cons X A) B :- rev A A', append A' (cons X nil) B.

select (cons X A) X A.
select (cons Y A) X (cons Y B) :- select A X B.

perm nil nil.
perm (cons X A') B :- select B X B', perm A' B'.
