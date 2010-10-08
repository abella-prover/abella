module add.

nat z.
nat (s N) :- nat N.

add z N N.
add (s N1) N2 (s N3) :- add N1 N2 N3.

lesseq z N.
lesseq (s N1) (s N2) :- lesseq N1 N2.

