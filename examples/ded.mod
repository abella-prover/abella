% K combinator
hil (imp A (imp B A)).

% S combinator
hil (imp (imp A (imp B C)) (imp (imp A B) (imp A C))).

% Modus ponens
hil B :- hil (imp A B), hil A.
