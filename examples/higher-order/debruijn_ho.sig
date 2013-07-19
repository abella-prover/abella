sig debruijn_ho.

% Translating lambda terms into the debruijn form

kind nat type.
type z nat.
type s nat -> nat.
type add nat -> nat -> nat -> o.

kind hterm type.
type app hterm -> hterm -> hterm.
type lam (hterm -> hterm) -> hterm.

kind dterm type.
type dapp dterm -> dterm -> dterm.
type dlam dterm -> dterm.
type dvar nat -> dterm.

type ho2db hterm -> nat -> dterm -> o.