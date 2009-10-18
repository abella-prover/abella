%% Euclid's GCD algorithm
%%
%% Adapted from the %reduces example in the Twelf User's Guide:
%% http://www.cs.cmu.edu/~twelf/guide-1-4/twelf_8.html#SEC47

module gcd.

nat z.
nat (s N) :- nat N.

bool tt.
bool ff.

sub X z X.
sub (s X) (s Y) Z :- sub X Y Z.

less z (s X) tt.
less X z ff.
less (s X) (s Y) B :- less X Y B.

lt z (s Y).
lt (s X) (s Y) :- lt X Y.

gcd z Y Y.
gcd X z X.
gcd (s X) (s Y) Z :- less X Y tt, sub Y X Y', gcd (s X) Y' Z.  % (1)
gcd (s X) (s Y) Z :- less X Y ff, sub X Y X', gcd X' (s Y) Z.  % (2)
