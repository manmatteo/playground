module lkf-polarize.

% Relates cforms to polarized formulas.  Highly non-deterministic if first argument only is fixed. 
polarize tt t+  &  polarize tt t-.
polarize ff f+  &  polarize ff f-.
polarize (B and C) (B' &-& C') &
polarize (B and C) (B' &+& C') &
polarize (B or  C) (B' !-! C') &
polarize (B or  C) (B' !+! C') :- polarize B B', polarize C C'.
polarize (forall B) (all B')   &
polarize (exists B) (some B')  :- pi x\ polarize (B x) (B' x).
polarize A (n A) :- atomic A, polarize_neg A.
polarize A (p A) :- atomic A, polarize_pos A.
polarize (B imp C)   D :- polarize ((neg B) or C) D.
polarize (B equiv C) D :- polarize ((B imp C) and (C imp B)) D.

polarize (neg tt) f+  &  polarize (neg tt) t-.
polarize (neg ff) f+  &  polarize (neg ff) f-.
polarize (neg (B and C)) (B' !-! C') &
polarize (neg (B and C)) (B' !+! C') &
polarize (neg (B or  C)) (B' &-& C') &
polarize (neg (B or  C)) (B' &+& C') :- polarize (neg B) B', polarize (neg C) C'.
polarize (neg (forall B)) (some B')   &
polarize (neg (exists B)) (all  B')   :- pi x\ polarize (neg (B x)) (B' x).
polarize (neg (neg B)) C     :- polarize B C.
polarize (neg A) (p A)       :- atomic A, polarize_neg A.
polarize (neg A) (n A)       :- atomic A, polarize_pos A.
polarize (neg (B imp C))   D :- polarize (neg ((neg B) or C)) D.
polarize (neg (B equiv C)) D :- polarize (neg ((B imp C) and (C imp B))) D.

% Polarize a cform using all negative connectives when both are available.
polarize- tt t-.
polarize- ff f-.
polarize- (B and C) (B' &-& C') &
polarize- (B or  C) (B' !-! C') :- polarize- B B', polarize- C C'.
polarize- (forall B) (all B')   &
polarize- (exists B) (some B')  :- pi x\ polarize- (B x) (B' x).
polarize- A (n A)       :- atomic A, polarize_neg A.
polarize- A (p A)       :- atomic A, polarize_pos A.
polarize- (B imp C)   D :- polarize- ((neg B) or C) D.
polarize- (B equiv C) D :- polarize- ((B imp C) and (C imp B)) D.

polarize- (neg tt) f-.
polarize- (neg ff) t-.
polarize- (neg (B and C)) (B' !-! C') &
polarize- (neg (B or  C)) (B' &-& C') :- polarize- (neg B) B', polarize- (neg C) C'.
polarize- (neg (forall B)) (some B') &
polarize- (neg (exists B)) (all  B') :- pi x\ polarize- (neg (B x)) (B' x).
polarize- (neg (neg B)) C :- polarize- B C.
polarize- (neg A) (p A) :- atomic A, polarize_neg A.
polarize- (neg A) (n A) :- atomic A, polarize_pos A.
polarize- (neg (B imp C))   D :- polarize- (neg ((neg B) or C)) D.
polarize- (neg (B equiv C)) D :- polarize- (neg ((B imp C) and (C imp B))) D.

% Polarize a cform using all positive connectives when both are available.
polarize+ tt t+.
polarize+ ff f+.
polarize+ (B and C) (B' &+& C') &
polarize+ (B or  C) (B' !+! C') :- polarize+ B B', polarize+ C C'.
polarize+ (forall B) (all B')   &
polarize+ (exists B) (some B')  :- pi x\ polarize+ (B x) (B' x).
polarize+ A (n A)       :- atomic A, polarize_neg A.
polarize+ A (p A)       :- atomic A, polarize_pos A.
polarize+ (B imp C)   D :- polarize+ ((neg B) or C) D.
polarize+ (B equiv C) D :- polarize+ ((B imp C) and (C imp B)) D.

polarize+ (neg tt) f+.
polarize+ (neg ff) t+.
polarize+ (neg (B and C)) (B' !+! C') &
polarize+ (neg (B or  C)) (B' &+& C') :- polarize+ (neg B) B', polarize+ (neg C) C'.
polarize+ (neg (forall B)) (some B') &
polarize+ (neg (exists B)) (all  B') :- pi x\ polarize+ (neg (B x)) (B' x).
polarize+ (neg (neg B)) C :- polarize+ B C.
polarize+ (neg A) (p A) :- atomic A, polarize_neg A.
polarize+ (neg A) (n A) :- atomic A, polarize_pos A.
polarize+ (neg (B imp C))   D :- polarize+ (neg ((neg B) or C)) D.
polarize+ (neg (B equiv C)) D :- polarize+ (neg ((B imp C) and (C imp B))) D.

% Polarize a cform using all multiplicative connectives when both are available.
polarizeM tt t+.
polarizeM ff f-.
polarizeM (B and C) (B' &+& C') &
polarizeM (B or  C) (B' !-! C') :- polarizeM B B', polarizeM C C'.
polarizeM (forall B) (all B')   &
polarizeM (exists B) (some B')  :- pi x\ polarizeM (B x) (B' x).
polarizeM A (n A)       :- atomic A, polarize_neg A.
polarizeM A (p A)       :- atomic A, polarize_pos A.
polarizeM (B imp C)   D :- polarizeM ((neg B) or C) D.
polarizeM (B equiv C) D :- polarizeM ((B imp C) and (C imp B)) D.

polarizeM (neg tt) f-.
polarizeM (neg ff) t+.
polarizeM (neg (B and C)) (B' !-! C') &
polarizeM (neg (B or  C)) (B' &+& C') :- polarizeM (neg B) B', polarizeM (neg C) C'.
polarizeM (neg (forall B)) (some B') &
polarizeM (neg (exists B)) (all  B') :- pi x\ polarizeM (neg (B x)) (B' x).
polarizeM (neg (neg B)) C :- polarizeM B C.
polarizeM (neg A) (p A) :- atomic A, polarize_neg A.
polarizeM (neg A) (n A) :- atomic A, polarize_pos A.
polarizeM (neg (B imp C))   D :- polarizeM (neg ((neg B) or C)) D.
polarizeM (neg (B equiv C)) D :- polarizeM (neg ((B imp C) and (C imp B))) D.
