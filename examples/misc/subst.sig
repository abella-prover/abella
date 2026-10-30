sig subst.

kind    tm      type.

type    app     tm -> tm -> tm.
type    abs     (tm -> tm) -> tm.

type    term    tm -> o.
type    copy    tm -> tm -> o.
type    subst   (tm -> tm) -> tm -> tm -> o.
