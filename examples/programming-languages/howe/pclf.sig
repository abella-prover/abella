sig pclf.

kind ty type.

type top  ty.
type arr  ty -> ty -> ty.
type list ty -> ty.

kind tm type.

type app   tm -> tm -> tm.
type lam   (tm -> tm) -> tm.
type fix   (tm -> tm) -> tm.
type unit  tm.
type nill  tm.
type cons  tm -> tm -> tm.
type lcase tm -> tm -> (tm -> tm -> tm) -> tm.

type ty    ty -> o.
type of    tm -> ty -> o.

type cp    tm -> tm -> o.