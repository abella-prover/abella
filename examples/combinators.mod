% Natural deduction
nd (imp A B) :- nd A => nd B.      % implies introduction
nd B :- nd (imp A B), nd A.        % implies eliminator

% Combinator reasoning
comb (imp A (imp B A)).                                   % K combinator
comb (imp (imp A (imp B C)) (imp (imp A B) (imp A C))).   % S combinator 
comb B :- comb (imp A B), comb A.                         % Modus ponens
