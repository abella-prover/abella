sig bred.

kind tm   type.
type lam  (tm -> tm) -> tm.
type app  tm -> tm -> tm.
type beta (tm -> tm) -> tm -> tm.

kind p type.
type left,right p -> p.
type bnd  (p -> p) -> p.
type done p.

type is_tm tm -> o.
type is_p  p -> o.

type bred tm -> tm -> o.

type path tm -> p -> o.

type bfree tm -> o.
