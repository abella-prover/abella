module mappred.

exist P :- P X.
and P Q :- P, Q.

mappred P anil anil.
mappred P (acons X XS) (acons Y YS) :- P X Y, mappred P XS YS.

swap P X Y :- P Y X.
