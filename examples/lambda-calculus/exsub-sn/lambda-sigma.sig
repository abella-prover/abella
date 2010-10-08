sig lambda-sigma.

accum_sig sigma-strong.

kind    tm, sub, ty, ctx      type.
kind    steptype  type.

type    base        ty.
type    arrow       ty -> ty -> ty.

type    empty       ctx.
type    cons        ctx -> ty -> ctx.

type    c           ty -> tm.
type    var         nat -> tm.
type    clos        tm -> sub -> tm.
type    app         tm -> tm -> tm.
type    lam         tm -> tm.

type    shift       nat -> sub.
type    dot         tm -> sub -> sub.
type    comp        sub -> sub -> sub.

type    wsnf        tm -> o.
type    wssnf       sub -> o.

type    su          steptype.
type    be          steptype.

type    convtm      tm -> exp -> o.
type    convsub     sub -> exp -> o.

type    step        steptype -> tm -> tm -> o.
type    steps       steptype -> sub -> sub -> o.
type    ty          ty -> o.
type    ctx         ctx -> o.
type    tm          tm -> o.
type    sub         sub -> o.

