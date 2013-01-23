sig breduce.

kind tm   type.
type abs  (tm -> tm) -> tm.
type app  tm -> tm -> tm.
type beta (tm -> tm) -> tm -> tm.

kind p type.
type left,right p -> p.
type bnd  (p -> p) -> p.

type bred tm -> tm -> o.

type path tm -> p -> o.

type bfree tm -> o.
type tm    tm -> o.