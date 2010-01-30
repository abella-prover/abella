%% Ralph Loader's proof of standardization
%%   (Notes on Simply Typed Lambda Calculus, ECS-LFCS-98-381)
%% an adaption of Hongwei Xi's arithmetical proof
%%   (Upper bounds for standardizations and an application, JSL 1999)
%% to Gordon Plotkin's inductive formulation of standard reduction.
%%   (Call-by-name, Call-by-value and the Lambda-Calculus, TCS 1975)
%%
%% Abella proof by Andreas Abel (October 2009)

module sred.

% pure lambda terms
tm (app M N) :- tm M, tm N.
tm (abs R) :- pi x\ tm x => tm (R x).

% ordinary one-step beta reduction
beta (app M N) (app M' N) :- beta M M'.
beta (app M N) (app M N') :- beta N N'.
beta (abs S1) (abs S2) :- pi x\ beta (S1 x) (S2 x).
beta (app (abs R) M) (R M).

% beta sequences as snoc lists
betas M M.
betas M N :- betas M P, beta P N.

% one-step weak head reduction
wh (app (abs R) M) (R M).
wh (app M N) (app M' N) :- wh M M'.

% Plotkin's standard reduction
sred M1 M3 :- wh M1 M2, sred M2 M3.
sred (app M1 N1) (app M2 N2) :- sred M1 M2, sred N1 N2.
sred (abs R1) (abs R2) :- pi x\ sred x x => sred (R1 x) (R2 x).
