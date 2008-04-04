% Natural deduction
nd (imp A B) :- nd A => nd B.
nd B :- nd (imp A B), nd B.
nd (and A B) :- nd A, nd B.

% Sequent calculus
conc A :- hyp A.                                     % init
conc (imp A B) :- hyp A => conc B.                   % impR
conc C :- hyp (imp A B), conc A, hyp B => conc C.    % impL
conc (and A B) :- conc A, conc B.                    % andR
conc C :- hyp (and A B), hyp A => hyp B => conc C.   % andL
conc B :- hyp A => conc B, conc A.                   % cut
