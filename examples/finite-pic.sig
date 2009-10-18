sig finite-pic.

% Three syntactic types are used: name (for names), action (for
% actions), and proc (for processes).  The type o denotes the type of
% propositions.

% The constructors for proc are 'null', 'taup', 'match', 'plus',
% 'par', and 'nu' denote, respectively, the mull process, the tau
% prefix, match prefix, the non-deterministic choice operator, the
% parallel composition, and the restriction operator of the
% pi-calculus. The input and output prefixes are encoded as in and
% out.

kind name, proc   type.

type null         proc.
type taup         proc -> proc.
type plus, par    proc -> proc -> proc.
type match, out   name -> name -> proc -> proc.
type in           name -> (name -> proc) -> proc.
type nu           (name -> proc) -> proc.

kind action       type.
type tau          action.
type up, dn       name -> name -> action.

% One step transition for free transitions
type one          proc ->          action  ->          proc  -> o.
% One step transition for binding transitions
type oneb         proc -> (name -> action) -> (name -> proc) -> o.
