module typing.

accumulate lambda-sigma.

of G (c A) A :- ty A.
of (cons G A) (var z) A.
of (cons G A) (var (s N)) B :- of G (var N) B.
of G (clos M S) A :- ofs G S G', of G' M A.
of G (app M N) B :- of G M (arrow A B), of G N A.
of G (lam R) (arrow A B) :- ty A, of (cons G A) R B.

ofs G (shift z) G.
ofs (cons G A) (shift (s N)) G' :- ofs G (shift N) G'.
ofs G (dot M S) (cons G' A) :- of G M A, ofs G S G'.
ofs G (comp S S') G' :- ofs G S' G'', ofs G'' S G'.

