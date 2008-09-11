% bound input
onep (in X M) (dn X) M.

% free output
one (out X Y P) (up X Y) P.

% tau
one  (taup P) tau P.

% match prefix
one  (match X X P) A Q :- one P A Q.
onep (match X X P) A M :- onep P A M.

% sum
one  (plus P Q) A R :- one  P A R.
one  (plus P Q) A R :- one  Q A R.
onep (plus P Q) A M :- onep P A M.
onep (plus P Q) A M :- onep Q A M.

% par
one  (par P Q) A (par P1 Q) :- one P A P1.
one  (par P Q) A (par P Q1) :- one Q A Q1.
onep (par P Q) A (x\par (M x) Q) :- onep P A M.
onep (par P Q) A (x\par P (N x)) :- onep Q A N.

% restriction
one  (nu x\P x) A (nu x\Q x)      :- pi x\ one  (P x) A (Q x).
onep (nu x\P x) A (y\ nu x\Q x y) :- pi x\ onep (P x) A (y\ Q x y).

% open
onep (nu x\M x) (up X) N :- pi y\ one (M y) (up X y) (N y).

% close
one (par P Q) tau (nu y\ par (M y) (N y)) :-
  onep P (dn X) M, onep Q (up X) N.
one (par P Q) tau (nu y\ par (M y) (N y)) :-
  onep P (up X) M, onep Q (dn X) N.

% comm
one (par P Q) tau (par (M Y) T) :-
  onep P (dn X) M, one Q (up X Y) T.
one (par P Q) tau (par R (M Y)) :-
  onep Q (dn X) M, one P (up X Y) R.

% Rep-act
one  (bang P) A (par P1 (bang P)) :- one P A P1.
onep (bang P) X (y\ par (M y) (bang P)) :- onep P X M.

% Rep-com
one (bang P) tau (par (par R (M Y)) (bang P)) :-
  onep P (dn X) M, one P (up X Y) R.

% Rep-close
one (bang P) tau (par (nu y\ par (M y) (N y)) (bang P)) :-
  onep P (up X) M, onep P (dn X) N.
