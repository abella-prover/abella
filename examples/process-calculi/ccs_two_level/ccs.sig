sig ccs.

kind    proc, act      type.

type    a, tau         act .
type    bar            act -> act .

type    null           proc.
type    out            act -> proc -> proc.
type    plus, par      proc -> proc -> proc.
type    mu             (proc -> proc) -> proc.

type    comp           act -> act -> o.
type    step           proc -> act -> proc -> o.
