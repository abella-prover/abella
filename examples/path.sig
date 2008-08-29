%% The specification in path.(sig|mod) can be executed by Teyjus
%%   http://teyjus.googlecode.com/
%% After installing Teyjus you can compile and run this as follows,
%%   tjcc path
%%   tjlink path
%%   tjsim path

sig path.

kind      tm        type.
kind      path      type.

type      app       tm -> tm -> tm.
type      abs       (tm -> tm) -> tm.

type      done      path.
type      fst       path -> path.
type      snd       path -> path.
type      bnd       (path -> path) -> path.

type      tm        tm -> o.
type      path      tm -> path -> o.
