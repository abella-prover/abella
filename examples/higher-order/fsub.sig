sig fsub.

% Subtyping relation in Fsub

kind tp         type.
type top        tp.
type arr        tp -> tp -> tp.
type all        tp -> (tp -> tp) -> tp.

%type tp         tp -> o.
type sub        tp -> tp -> o.
