sig processes_terms.

kind pt type.

%lsc terms
type abs (pt -> pt) -> pt.
type app pt -> pt -> pt.
type subex (pt -> pt) -> pt -> pt.

%pi-calculus terms
type null       pt.
type nu 	(pt -> pt) -> pt.
type par	pt -> pt -> pt.
type out	pt -> pt -> pt.
type out2	pt -> pt -> pt -> pt.
type in		pt -> (pt -> pt) -> pt.
type in2 	pt -> (pt -> pt -> pt) -> pt.