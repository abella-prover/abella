sig eval.

kind    tm, ty                 type.

type    app                    tm -> tm -> tm.
type    abs                    (tm -> tm) -> tm.

type    arrow                  ty -> ty -> ty.

type    of                     tm -> ty -> o.
type    eval, step, nstep      tm -> tm -> o.
