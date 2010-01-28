module ees.

% The system L_{+,->}

% Closed natural numbers
natural z.
natural (s N) :- natural N.

% Closed types
typ nat.
typ (arr T1 T2) :- typ T1, typ T2.

% Static semantics
of (num N) nat :- natural N.
of (plus E1 E2) nat :- of E1 nat, of E2 nat.
of (lam T1 E2) (arr T1 T2) :- typ T1, pi x\ of x T1 => of (E2 x) T2.
of (app E1 E2) T :- of E1 (arr T2 T), of E2 T2.

% Primitive addition operation
sum z N2 N2 :- natural N2.
sum (s N1) N2 (s N3) :- sum N1 N2 N3.

% Values
val (num N) :- natural N.
val (lam T1 E2).

% Evaluation
eval (num N) (num N) :- natural N.
eval (plus E1 E2) (num N) :- eval E1 (num N1), eval E2 (num N2), sum N1 N2 N.
eval (lam T1 E2) (lam T1 E2).
eval (app E1 E2) V :- eval E1 (lam T E), eval E2 V2, eval (E V2) V.
