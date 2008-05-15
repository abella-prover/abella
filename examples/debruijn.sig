%% The specification in debrjuin.(sig|mod) can be executed by Teyjus
%%   http://teyjus.googlecode.com/
%% After installing Teyjus you can compile and run this as follows,
%%   tjcc debruijn
%%   tjlink debruijn
%%   tjsim debruijn

sig debruijn.

kind      nat       type.
type      z         nat.
type      s         nat -> nat.
type      add       nat -> nat -> nat -> o.

kind      hterm     type.
type      app       hterm -> hterm -> hterm.
type      lam       (hterm -> hterm) -> hterm.

kind      dterm     type.
type      dapp      dterm -> dterm -> dterm.
type      dlam      dterm -> dterm.
type      dvar      nat -> dterm.

type      ho2db     hterm -> nat -> dterm -> o.
type      depth     hterm -> nat -> o.
