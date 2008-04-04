%% Natural deduction

nd (imp A B) :- nd A => nd B.
nd B :- nd (imp A B), nd B.


%% Sequent calculus

conc A :- hyp A.                                     % init
conc B :- hyp A => conc B, conc A.                   % cut

conc (imp A B) :- hyp A => conc B.                   % impR
conc C :- hyp (imp A B), conc A, hyp B => conc C.    % impL
