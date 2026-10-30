module equiv.

% Natural deduction
nd (imp A B) :- nd A => nd B.      % implies introduction
nd B :- nd (imp A B), nd A.        % implies elimination

% Hilbert calculus
hil (imp A (imp B A)).                                   % K combinator
hil (imp (imp A (imp B C)) (imp (imp A B) (imp A C))).   % S combinator
hil B :- hil (imp A B), hil A.                           % Modus ponens

%% Sequent calculus
conc A :- hyp A.                                     % init
conc B :- hyp A => conc B, conc A.                   % cut

conc (imp A B) :- hyp A => conc B.                   % impR
conc C :- hyp (imp A B), conc A, hyp B => conc C.    % impL
