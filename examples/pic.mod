% A specification of the late transition system for the pi calculus.

module pic.

% Syntactic equality
eq X X.

% bound input
oneb (in X M) (dn X) M.

% free output
one (out X Y P) (up X Y) P.

% tau 
one  (taup P) tau P.

% match prefix
one  (match X X P) A Q :- one P A Q.
oneb (match X X P) A M :- oneb P A M.

% sum
one  (plus P Q) A R :- one  P A R.
one  (plus P Q) A R :- one  Q A R.
oneb (plus P Q) A M :- oneb P A M.
oneb (plus P Q) A M :- oneb Q A M.

% par
one  (par P Q) A (par P1 Q) :- one P A P1.
one  (par P Q) A (par P Q1) :- one Q A Q1.
oneb (par P Q) A (x\par (M x) Q) :- oneb P A M.
oneb (par P Q) A (x\par P (N x)) :- oneb Q A N.

% restriction
one  (nu x\P x) A (nu x\Q x)      :- pi x\ one  (P x) A (Q x).
oneb (nu x\P x) A (y\ nu x\Q x y) :- pi x\ oneb (P x) A (y\ Q x y).

% open 
oneb (nu x\M x) (up X) N :- pi y\ one (M y) (up X y) (N y).

% close
one (par P Q) tau (nu y\ par (M y) (N y)) :-
oneb P (dn X) M , oneb Q (up X) N.
one (par P Q) tau (nu y\ par (M y) (N y)) :-
oneb P (up X) M , oneb Q (dn X) N.

% comm
one (par P Q) tau (par R T) :-
oneb P (dn X) M, one Q (up X Y) T, eq R (M Y).
one (par P Q) tau (par R T) :-
oneb Q (dn X) M,  one P (up X Y) R, eq T (M Y).

one (bang P) A (par Q (bang P)) :- one P A Q.
oneb (bang P) X (y\ par (M y) (bang P)) :- oneb P X M.
one (bang P) tau (par (par Q R) (bang P)) :- one P (up X Y) Q, oneb P (dn X) M, eq R (M Y).
one (bang P) tau (par (nu z\ par (M z) ( N z)) (bang P)) :- 
  oneb P (up X) M, oneb P (dn X) N.
