sig strong-ext.

accum_sig strong-norm.

kind    congtype  type.

type    noc          congtype.
type    clo          congtype.

% congtype specifies whether the step uses the closure congruence rule
type    step1        congtype -> nat -> steptype -> tm -> tm -> o.
type    step1s       congtype -> nat -> steptype -> sub -> sub -> o.

type    mstep1_clo    nat -> tm -> tm -> o.
type    mstep1s_clo   nat -> sub -> sub -> o.
type    mstep1        nat -> tm -> tm -> o.
type    mstep1s       nat -> sub -> sub -> o.

type    wcomp        nat -> sub -> sub -> o.

type    tme          tm -> o.
type    sube         sub -> o.

