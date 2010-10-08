sig sigma-strong.

accum_sig add.

kind    exp      type.

type    ec          exp.
type    evar        nat -> exp.
type    eshift      nat -> exp.
type    eclos       exp -> exp -> exp.
type    edot        exp -> exp -> exp.
type    elam        exp -> exp.

type    estep       exp -> exp -> o.
type    exp         exp -> o.
type    subexp      exp -> exp -> o.

