module lists.

list nl.
list (cons X L) :- list L.

append nl C C.
append (cons X A) B (cons X C) :- append A B C.

rev nl nl.
rev (cons X A) B :- rev A A', append A' (cons X nl) B.

select (cons X A) X A.
select (cons Y A) X (cons Y B) :- select A X B.

perm nl nl.
perm (cons X A') B :- select B X B', perm A' B'.
