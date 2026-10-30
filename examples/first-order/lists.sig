sig lists.

kind    i, lst       type.

type    nl            lst.
type    cons          i -> lst -> lst.

type    list          lst -> o.
type    append        lst -> lst -> lst -> o.
type    rev, perm     lst -> lst -> o.
type    select        lst -> i -> lst -> o.
