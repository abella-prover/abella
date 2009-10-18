sig sn2.

kind    tm, ty      type.

type    app         tm -> tm -> tm.
type    abs         ty -> (tm -> tm) -> tm.

type    top         ty.
type    arrow       ty -> ty -> ty.

type    ty          ty -> o.
type    of          tm -> ty -> o.
type    step, cp    tm -> tm -> o.
