% From Dale Miller:
%
% It is easy to write code that determines if a given lambda-term (type
% tm) is in beta-normal form (using the fact that a term in normal form
% is of the form (lambda x1 ... lambda xn. h t1 ... tn) where t1, ...,
% tn are in beta-normal form and h is a variable (one of the x1, ...,
% xn, or a variable introduced before).  It is also possible to know
% that a term is not in beta-normal form since it contains a beta-redex
% (in abstract syntax, it would contain a subterm of the form (app (abs
% R) M).  An interesting theorem to try is the one that says
%   forall T : tm.  (normal T) or (non-normal T).
% This one should have a simple proof if the right induction invariant
% can be stated.

module normal.

term (app M N) :- term M, term N.
term (abs R) :- pi x\ term x => term (R x).


non_normal (app (abs R) M).
non_normal (app M N) :- non_normal M.
non_normal (app M N) :- non_normal N.
non_normal (abs R) :- pi x\ non_normal (R x).

normal (abs R) :- pi x\ neutral x => normal (R x).
normal M :- neutral M.
neutral (app M N) :- neutral M, normal N.
