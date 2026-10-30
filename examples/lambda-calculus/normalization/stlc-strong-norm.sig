sig stlc-strong-norm.

kind    tm, ty      type.

type    c           tm.
type    app         tm -> tm -> tm.
type    abs         ty -> (tm -> tm) -> tm.

type    top         ty.
type    arrow       ty -> ty -> ty.

type    ty          ty -> o.
type    of          tm -> ty -> o.
type    step        tm -> tm -> o.
