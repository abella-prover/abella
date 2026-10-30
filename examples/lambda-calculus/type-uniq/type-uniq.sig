sig type-uniq.

kind    tm, ty    type.

type    app       tm -> tm -> tm.
type    abs       ty -> (tm -> tm) -> tm.

type    arrow     ty -> ty -> ty.

type    of        tm -> ty -> o.
