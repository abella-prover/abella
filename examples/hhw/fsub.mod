module fsub.

% Subtyping relation in Fsub

sub T top.
sub (arr S1 S2) (arr T1 T2) :- sub T1 S1, sub S2 T2.
sub (all S1 S2) (all T1 T2) :- 
    sub T1 S1, 
    pi a\ 
      (pi U\ pi V\ sub a U => sub U V => sub a V) =>
      sub a T1 => 
      sub a a =>
        sub (S2 a) (T2 a).