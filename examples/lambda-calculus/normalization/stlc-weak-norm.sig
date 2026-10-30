sig stlc-weak-norm.

kind    tm, ty         type.

type    app            tm -> tm -> tm.
type    abs            ty -> (tm -> tm) -> tm.

type    top            ty.
type    arrow          ty -> ty -> ty.

type    value          tm -> o.
type    of             tm -> ty -> o.
type    step, steps    tm -> tm -> o.
