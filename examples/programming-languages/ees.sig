sig ees.

% Natural numbers
kind natural    type.
type z          natural.
type s          natural -> natural.

% Syntactic category of types
kind typ        type.
type nat        typ.
type arr        typ -> typ -> typ.

% Syntactic category of expressions
kind exp        type.
type num        natural -> exp.
type plus       exp -> exp -> exp.
type lam        typ -> (exp -> exp) -> exp.
type app        exp -> exp -> exp.

% Static semantics
type natural    natural -> o.
type typ        typ -> o.
type of         exp -> typ -> o.

% Dynamic (evaluation) semantics
type sum        natural -> natural -> natural -> o.
type val        exp -> o.
type eval       exp -> exp -> o.
