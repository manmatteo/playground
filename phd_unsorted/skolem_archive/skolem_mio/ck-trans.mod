% Procedures for translating from client-side terms (containing Skolem
% functions) to kernel-side terms (containing eigenvariables).

module ck-trans.

rigid T           :- not (T = dummy).
ready    (cp T S) :- rigid T.
notready (cp T S) :- not (rigid T).

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

% Also, dummy must be exported but not used (it cannot be hidden).

ck_translate T T' :- cc_interp [] [cp T T'].
