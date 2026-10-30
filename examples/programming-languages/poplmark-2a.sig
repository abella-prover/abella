sig poplmark-2a.

kind     tm, ty     type.

type     top        ty.
type     arrow      ty -> ty -> ty.
type     all        ty -> (ty -> ty) -> ty.

type     abs        ty -> (tm -> tm) -> tm.
type     app        tm -> tm -> tm.
type     tabs       ty -> (ty -> tm) -> tm.
type     tapp       tm -> ty -> tm.

type     sub        ty -> ty -> o.
type     of         tm -> ty -> o.
type     value      tm -> o.
type     step       tm -> tm -> o.
