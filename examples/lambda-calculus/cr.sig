sig cr.

kind     tm                type.

type     app               tm -> tm -> tm.
type     abs               (tm -> tm) -> tm.

type     trm, notabs       tm -> o.
type     pr1, cd1          tm -> tm -> o.
type     beta, betan       tm -> tm -> o.
