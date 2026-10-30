sig normal.

kind      tm                     type.

type      app                    tm -> tm -> tm.
type      abs                    (tm -> tm) -> tm.

type      term                   tm -> o.
type      non_normal             tm -> o.
type      neutral, normal        tm -> o.
