module cforms.

non_atomic tt         & non_atomic ff.
non_atomic (neg _).
non_atomic (_ and _)  & non_atomic (_ or _).
non_atomic (_ imp _)  & non_atomic (_ equiv _).
non_atomic (forall _) & non_atomic (exists _).

atomic A :- non_atomic A, !, fail.  % NAF here.
atomic A.

literal A       :- atomic A.
literal (neg A) :- atomic A.

% Negation normal form.

nnf tt tt.
nnf ff ff.
nnf (B and C) (B' and C') &
nnf (B or  C) (B' or  C') :- nnf B B', nnf C C'.
nnf (forall B) (forall B') &
nnf (exists B) (exists B') :- pi x\ nnf (B x) (B' x).
nnf (B imp C)   D :- nnf ((neg B) or C) D.
nnf (B equiv C) D :- nnf ((B imp C) and (C imp B)) D.
nnf A A :- atomic A.

nnf (neg tt) ff.
nnf (neg ff) tt.
nnf (neg (neg A)) B :- nnf A B.
nnf (neg (B and C)) (B' or  C') &
nnf (neg (B or  C)) (B' and C') :- nnf (neg B) B', nnf (neg C) C'.
nnf (neg (forall B)) (exists B') &
nnf (neg (exists B)) (forall B') :- pi x\ nnf (neg (B x)) (B' x).
nnf (neg (B imp C))   D :- nnf (B and (neg C)) D.
nnf (neg (B equiv C)) D :- nnf (neg ((B imp C) and (C imp B))) D.
nnf (neg A) (neg A) :- atomic A.
