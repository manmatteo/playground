module ljf-formulas.

isNegAtm (n _).
isPosAtm (p _).

isNegForm (_ and- _) & isNegForm (_ arr _).
isNegForm (all _)   & isNegForm (d- _)    & isNegForm t-.
isNeg A :- isNegForm A ; isNegAtm A.

isPosForm (_ or+ _) & isPosForm (_ and+ _).
isPosForm (d+ _)    & isPosForm (some _)  & isPosForm f  &  isPosForm t+.
isPos A :- isPosForm A ; isPosAtm A.


