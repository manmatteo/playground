module mimic-fpc.

/* mimic */
arr_jc (mimic I) (aphaseL I [] [I] I).
decideL_je (aphaseR I Cs X) (sphaseL Cs I X) I.
decideR_je (aphaseR I Cs I) (sphaseR Cs   I).
storeL_jc (aphaseL Rt Cs [I,J|R] X) (aphaseL Rt Cs [J|R] X) I.
storeL_jc (aphaseL Rt Cs [I] X)     (aphaseR Rt Cs X) I.
storeR_jc (aphaseR Rt Cs X)         (aphaseR Rt Cs X).
initialL_je (sphaseL _ I I).
initialR_je (sphaseR _   I) I.
releaseL_je (sphaseL _ I X) (aphaseL I [] [I] X).
releaseR_je (sphaseR _   I) (aphaseR I []     I).
arr_jc    (aphaseR Rt Cs I) (aphaseL Rt Cs [mL I] (mR I)).
andNeg_jc (aphaseR Rt Cs I) (aphaseR Rt [mL I|Cs] (mL I))
                            (aphaseR Rt [mR I|Cs] (mR I)).
andPos_jc (aphaseL Rt Cs [I|R] X) (aphaseL Rt Cs [mL I, mR I|R] X).
true_jc   (aphaseL Rt Cs [I,J|R] X) (aphaseL Rt Cs [J|R] X).
true_jc   (aphaseL Rt Cs [I] X)     (aphaseR Rt Cs X).
or_jc     (aphaseL Rt Cs [I|R] X) (aphaseL Rt [mL I|Cs] [mL I|R] X)
                                  (aphaseL Rt [mR I|Cs] [mR I|R] X).
arr_je    (sphaseL Cs I X) (sphaseR Cs (mL I)) (sphaseL Cs (mR I) X).
andPos_je (sphaseR Cs   I) (sphaseR Cs (mL I)) (sphaseR Cs (mR I)).
true_je   (sphaseR Cs I).
or_je     (sphaseR Cs I)   (sphaseR Cs' (mL I))   left  &
andNeg_je (sphaseL Cs I X) (sphaseL Cs' (mL I) X) left  :-
          memb_and_rest (mL I) Cs Cs'.
or_je     (sphaseR Cs I)   (sphaseR Cs' (mR I))   right &
andNeg_je (sphaseL Cs I X) (sphaseL Cs' (mR I) X) right :-
          memb_and_rest (mR I) Cs Cs'.

% type some_jc, all_jc               cert -> (i -> cert) -> prop.
% some_jc (aphaseL Rt Cs [I|R] X) (Eigen\ aphaseL Rt Cs [mD I|R] X).
% all_jc (aphaseR Rt Cs I) (Eigen\ aphaseR Rt Cs (mD I)).

some_jc (aphaseL Rt Cs [I|R] X) (Eigen\ aphaseL Rt Cs [I|R] X).
all_jc (aphaseR Rt Cs I) (Eigen\ aphaseR Rt Cs (I)).

% type some_je, all_je               cert -> cert -> i -> prop.
%some_je (sphaseR Cs I) (sphaseR Cs' (mD I)) Term.        
%all_je (sphaseL Cs I X) (sphaseL Cs (mD I) X) Term.

some_je (sphaseR Cs I) (sphaseR Cs' (I)) Term.        
all_je (sphaseL Cs I X) (sphaseL Cs ( I) X) Term.

/* end */

% Note that there are two clauses for storeL_jc and true_jc since they
% may need to make a transition to the asyncR phase.
