module coc-ljf.
axiom p t.
rel p p p. rel p t t. rel t p p. rel t t t.

% async A B :- print "async" A B, fail.
% astr A B :- print "astr" A B, fail.
% sync A B C :- print "sync" A B C, fail.

%% sort
async (sort X) C :-
  beta C (sort Y),
  axiom X Y.
%% ax (negative atoms)
sync nil A B :-
  beta A B.

%% structural
astr (app ( Var :: L )) R :-
  store Var N,% isneg N,
  sync L N R.
async Tm Ty :-
  negatm Ty, %; ispos Ty 
  astr Tm Ty.

%% async (pi-r+store), (pi-wf)
async (fun _ Ty T) C :-
  beta C (prod _ Ty Ty'),
  pi w\ store w Ty => negatm Ty =>
    async (T w) (Ty' w).
async (prod A B) C :-
  beta C (sort S3),
  rel S1 S2 S3,
  async A (sort S1),
  pi w\ store w A => negatm A => async (B w) (sort S2).

%% sync (pi-l)
sync Cert L R :-
  beta L (prod Ty1 Ty2),
  pi_e (Cert Tm) Cert1 (Cert2 Tm),
  asyncr Cert1 Ty1,
  sync Cert2 (Ty2 Tm) R.
  
beta X X.
