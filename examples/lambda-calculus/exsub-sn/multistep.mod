module multistep.

accumulate lambda-sigma.

mstep0 M M.
mstep0 M1 M3 :- step T M1 M2, mstep0 M2 M3.
msteps0 S S.
msteps0 S1 S3 :- steps T S1 S2, msteps0 S2 S3.
mstep M1 M3 :- step T M1 M2, mstep0 M2 M3.
msteps S1 S3 :- steps T S1 S2, msteps0 S2 S3.

mstep_su0 M M.
mstep_su0 M1 M3 :- step su M1 M2, mstep_su0 M2 M3.
msteps_su0 S S.
msteps_su0 S1 S3 :- steps su S1 S2, msteps_su0 S2 S3.
mstep_su M1 M3 :- step su M1 M2, mstep_su0 M2 M3.
msteps_su S1 S3 :- steps su S1 S2, msteps_su0 S2 S3.

