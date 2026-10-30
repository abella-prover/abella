sig path.

kind    tm, path          type.

type    app               tm -> tm -> tm.
type    abs               (tm -> tm) -> tm.

type    done              path.
type    left, right       path -> path.
type    bnd               (path -> path) -> path.

type    tm                tm -> o.
type    path              tm -> path -> o.
