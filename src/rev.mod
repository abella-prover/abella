append nil C C.
append (cons X A) B (cons X C) :- append A B C.

rev nil nil.
rev (cons X A) B :- rev A A', append A' (cons X nil) B.

eq X X.
