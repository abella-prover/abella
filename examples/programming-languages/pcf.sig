sig pcf.

kind    tm, ty                   type.

type    zero, tt, ff             tm.
type    succ, pred, is_zero      tm -> tm.
type    if                       tm -> tm -> tm -> tm.
type    abs, rec                 ty -> (tm -> tm) -> tm.
type    app                      tm -> tm -> tm.

type    num, bool                ty.
type    arr                      ty -> ty -> ty.

type    eval                     tm -> tm -> o.
type    of                       tm -> ty -> o.
