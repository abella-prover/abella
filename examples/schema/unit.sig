sig unit.

kind    tm, ty, path   type.

type    app       tm -> tm -> tm.
type    abs       ty -> (tm -> tm) -> tm.

type    arrow     ty -> ty -> ty.


type    done              path.
type    left, right       path -> path.
type    bnd               (path -> path) -> path.


type    i         o.
type    of        tm -> ty -> o.
type    path      tm -> path -> o.

type    foo        ty -> ty.

type bred tm -> tm -> o.