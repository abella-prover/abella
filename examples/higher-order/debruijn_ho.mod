module debruijn_ho.

% Translating lambda terms into the debruijn form

add z C C.
add (s A) B (s C) :- add A B C.

% H here is the height (depth) of lambda abstractions
ho2db (app M N) H (dapp DM DN) :- ho2db M H DM, ho2db N H DN.
ho2db (lam R) H (dlam DR) :-
  pi x\ (pi H'\ pi DX\ add H DX H' => ho2db x H' (dvar DX)) =>
    ho2db (R x) (s H) DR.