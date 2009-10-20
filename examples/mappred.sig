sig mappred.

kind    a, alist        type.

type    anil            alist.
type    acons           a -> alist -> alist.

type    mappred         (a -> a -> o) -> alist -> alist -> o.

type    swap            (a -> a -> o) -> (a -> a -> o).

% We don't have these explicitly in Abella, but we can define them
type    and             o -> o -> o.
type    exist           (a -> o) -> o.
