module lkf-kernel.

% accumulate ck-trans. % This translation is really part of the kernel.

% lkf_entry A B  :- announce (lkf_entry A B).
% async A B  :- announce (async A B).
% sync  A B  :- announce (sync  A B).

lkf_entry Cert Form :- async Cert [Form].

async Cert nil :-
% spy(cutE Cert CertA CertB F),
  cutE Cert CertA CertB F,
  negate F NF, async CertA [F], async CertB [NF].

async Cert nil            :- 
% spy (decideE Cert Cert' I), 
 decideE Cert Cert' I, 
 storage I P, isPos P, sync Cert' P.

async Cert [t-|_].
async Cert [f-|Rest]        :- falseC Cert Cert', async Cert' Rest.
async Cert [d- A| Rest]     :- async Cert [A|Rest].
async Cert [(A !-! B)|Rest] :- orC Cert Cert', async Cert' [A, B|Rest].
async Cert [(A &-& B)|Rest] :- andC Cert CertA CertB, async CertA [A|Rest], async CertB [B|Rest].
async Cert [all B|Rest]     :- fix_bug Cert,
   allC Cert Cert',      pi w\          async (Cert' w) [B w|Rest].
async Cert [all B|Rest]     :-  
    allCx  Cert Cert' T, pi w\ (localcp T w) => async Cert'     [B w|Rest].
async Cert [all B|Rest]     :-  
    allCxx Cert Cert' T, pi w\ (localcp T w) => async (Cert' w) [B w|Rest].
async Cert [C|Rest]         :- (isPos C ; isNegAtm C), 
% spy (storeC Cert Cert' I),
 storeC Cert Cert' I,
 storage I C => async Cert' Rest.

sync Cert t+        :- trueE Cert.
sync Cert (d+ A)    :- sync Cert A.
sync Cert N         :- isNeg N, releaseE Cert Cert', async Cert' [N].
sync Cert (p A)     :- initialE Cert I, storage I (n A).
sync Cert (A &+& B) :- andE Cert CertA CertB, sync CertA A, sync CertB B.
sync Cert (A !+! B) :- orE Cert Cert' C, ((C = left,  sync Cert' A); (C = right, sync Cert' B)).

sync Cert (some B)  :- someE  Cert Cert' T, ck_translate T T', sync Cert' (B T').
sync Cert (some B)  :- someEx Cert Cert', sync Cert' (B T).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% DM killing off the suspension path - not used in current situation
%    More simplification is possible.

%rigid T           :- not (T = dummy).
ready    (cp T S).%  :- rigid T.
notready (cp T S) :- not (ready (cp T S)).

cc Body (cp T S) :-
  fun_pname T Name L,
  fun_pname S Name K,
  mappred2 (u\v\w\ w = cp u v) L K Body.

cc_interp [] [].
cc_interp Su []              :- forsome ready Su, !, cc_interp [] Suspend.
cc_interp Su (Goal :: Goals) :- notready Goal, spy(cc_interp (Goal :: Su) Goals).
cc_interp Su (Goal :: Goals) :- ready Goal,
  (cc Body Goal ; (localcp T S, Goal = (cp T S), Body = [])),
  append Body Goals New, cc_interp Su New.

% The only constants that need to be exported from this module are the
% ck_translate predicate (used in someE) and the localcp constant (use
% in allCx).

ck_translate T T' :- cc_interp [] [cp T T'].
