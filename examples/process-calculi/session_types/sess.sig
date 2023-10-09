sig sess.

kind tp type.

type one, bot  tp.
type tens, parr, with, plus tp -> tp -> tp.

type dual tp -> tp -> o.

kind nm type.
kind proc type.

type fwd nm -> nm -> proc.
type close nm -> proc.
type wait nm -> proc -> proc.
type inl, inr nm -> (nm -> proc) -> proc.
type choice nm -> (nm -> proc) -> (nm -> proc) -> proc.
type out nm -> (nm -> proc) -> (nm -> proc) -> proc.
type inp nm -> (nm -> nm -> proc) -> proc.
type nu tp -> (nm -> proc) -> (nm -> proc) -> proc.

type lin (nm -> proc) -> o.

type hyp nm -> tp -> o.
type wtp proc -> o.

type step  proc -> proc -> o.
type cong1 proc -> proc -> o.
type cong  proc -> proc -> o.
