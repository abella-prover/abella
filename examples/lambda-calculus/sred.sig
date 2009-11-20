%% Ralph Loader's proof of standardization
%% See his Lecture Notes on Typed Lambda Calculus
%%
%% Abella proof by Andreas Abel (October 2009)

sig sred.

kind    tm                          type.

type    app                         tm -> tm -> tm.
type    abs                         (tm -> tm) -> tm.

type    tm                          tm -> o.
type    beta, betas, wh, sred       tm -> tm -> o.
