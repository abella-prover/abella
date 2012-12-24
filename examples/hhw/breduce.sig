sig breduce.

kind tm   type.
type lam  (tm -> tm) -> tm.
type app  tm -> tm -> tm.
type beta (tm -> tm) -> tm -> tm.

kind path type.
type left,right path -> path.
type bnd  (path -> path) -> path.

type breduce tm -> tm -> o.

type path tm -> path -> o.

%type bfree tm -> o.
