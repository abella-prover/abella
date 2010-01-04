module hidden.

aux1 nill C C.
aux1 (cons X A) B C :- aux1 A (cons X B) C.

rev1 A B :- aux1 A nill B.

rev2 A B :-
  pi aux2\
    (pi C\ aux2 nill C C) =>
    (pi X\ pi A\ pi B\ pi C\ aux2 A (cons X B) C => aux2 (cons X A) B C) =>
      aux2 A nill B.

rev3 A B :-
  pi aux3\
    (aux3 nill B) =>
    (pi X\ pi A\ pi B\ aux3 A (cons X B) => aux3 (cons X A) B) =>
      aux3 A nill.
