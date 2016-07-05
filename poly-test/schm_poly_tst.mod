module schm_poly_tst.

app nil L L.
app (X :: L1) L2 (X :: L3) :- app L1 L2 L3.

pred (cst X).