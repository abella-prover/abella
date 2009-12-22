%% POPLmark 1a using Pientka's higher-order abstract syntax encoding

module poplmark-hohh.

sub S top.

sub (arrow S1 S2) (arrow T1 T2) :- sub T1 S1, sub S2 T2.

sub (all S1 (x\ S2 x)) (all T1 (x\ T2 x)) :-
    sub T1 S1,
    pi a\
      (pi U\ pi V\ sub U V => sub a U => sub a V) =>
      (sub a T1) =>
      (sub a a) =>
        sub (S2 a) (T2 a).

