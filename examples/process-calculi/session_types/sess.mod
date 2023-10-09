module sess.

dual one bot.
dual bot one.
dual (tens A B) (parr Ad Bd) :- dual A Ad, dual B Bd.
dual (parr A B) (tens Ad Bd) :- dual A Ad, dual B Bd.
dual (with A B) (plus Ad Bd) :- dual A Ad, dual B Bd.
dual (plus A B) (with Ad Bd) :- dual A Ad, dual B Bd.

lin (z\ fwd z Y).
lin (z\ fwd X z).
lin (z\ close z).
lin (z\ wait z P).
lin (z\ wait X (P z)) :- lin P.
lin (z\ out z P Q) :- lin P, lin Q.
lin (z\ out X (x\ P x z) Q) :- pi x\ lin (z\ P x z).
lin (z\ out X P (x\ Q x z)) :- pi x\ lin (z\ Q x z).
lin (z\ inp z (x\ y\ P x y)) :- (pi x\ lin (y\ P x y)), (pi y\ lin (x\ P x y)).
lin (z\ inp X (x\ y\ P x y z)) :- pi x\ pi y\ lin (z\ P x y z).
lin (z\ inl z (x\ P x)) :- lin P.
lin (z\ inl X (x\ P x z)) :- pi x\ lin (z\ P x z).
lin (z\ inr z (x\ P x)) :- lin P.
lin (z\ inr X (x\ P x z)) :- pi x\ lin (z\ P x z).
lin (z\ choice z (x\ P x) (x\ Q x)) :- lin P, lin Q.
lin (z\ choice X (x\ P x z) (x\ Q x z)) :-
  (pi x\ lin (z\ P x z)),
  (pi x\ lin (z\ Q x z)).
lin (z\ nu A (x\ P x z) Q) :-
  pi x\ lin (z\ P x z).
lin (z\ nu A P (x\ Q x z)) :-
  pi x\ lin (z\ Q x z).

wtp (fwd X Y) :- dual A B, hyp X A, hyp Y B.
wtp (close X) :- hyp X one.
wtp (wait X P) :- hyp X bot, wtp P.
wtp (out X P Q) :- hyp X (tens A B),
  (pi y\ hyp y A => wtp (P y)),
  (pi w\ hyp w B => wtp (Q w)).
wtp (inp X P) :- hyp X (parr A B),
  pi y\ hyp y A => pi w\ hyp w B => wtp (P y w).
wtp (inl X P) :- hyp X (plus A B),
  pi y\ hyp y A => wtp (P y).
wtp (inr X P) :- hyp X (plus A B),
  pi y\ hyp y B => wtp (P y).
wtp (choice X P Q) :- hyp X (with A B),
  (pi y\ hyp y A => wtp (P y)),
  (pi w\ hyp w B => wtp (Q w)).
wtp (nu A (x\ P x) (x\ Q x)) :- dual A B, lin P, lin Q,
  (pi x\ hyp x A => wtp (P x)),
  (pi y\ hyp y B => wtp (Q y)).

cong1 (nu A P Q)
      (nu B Q P) :- dual A B. % symmetry
cong1 (nu B (y\ nu A P (x\ Q x y)) R)
      (nu A P (x\ nu B (y\ Q x y) R)). % associativity
cong P P.
cong P R :- cong1 P Q, cong Q R.

% reductions (principal)
step (nu A (x\ fwd x Y) Q)
     (Q Y).
step (nu A (y\ fwd X y) Q)
     (Q X).                                        % [TODO] needed?
step (nu one (x\ close x) (x\ wait x Q))
     Q.
step (nu (tens A B) (x\ out x P1 P2) (x\ inp x Q))
     (nu A P1 (x\ nu B P2 (Q x))).
step (nu (plus A B) (x\ inl x P) (x\ choice x Q1 Q2))
     (nu A P Q1).
step (nu (plus A B) (x\ inr x P) (x\ choice x Q1 Q2))
     (nu B P Q2).
% commuting conversions
step (nu A (z\ wait X (P z)) Q)
     (wait X (nu A P Q)).
step (nu A (z\ out X (y\ P1 z y) P2) Q)
     (out X (y\ nu A (z\ P1 z y) Q) P2).
step (nu A (z\ out X P1 (y\ P2 z y)) Q)
     (out X P1 (y\ nu A (z\ P2 z y) Q)).
step (nu A (z\ inp X (y\ w\ P z y w)) Q)
     (inp X (y\ w\ nu A (z\ P z y w) Q)).
step (nu A (z\ inl X (y\ P z y)) Q)
     (inl X (y\ nu A (z\ P z y) Q)).
step (nu A (z\ inr X (y\ P z y)) Q)
     (inr X (y\ nu A (z\ P z y) Q)).
step (nu A (z\ choice X (y\ P1 z y) (y\ P2 z y)) Q)
     (choice X (y\ nu A (z\ P1 z y) Q) (y\ nu A (z\ P2 z y) Q)).
% congruence
step (nu A P Q) (nu A R Q) :- pi x\ step (P x) (R x).
step (nu A P Q) (nu A P R) :- pi x\ step (Q x) (R x).
% structure
step P S :- cong P Q, step Q R, cong R S.
