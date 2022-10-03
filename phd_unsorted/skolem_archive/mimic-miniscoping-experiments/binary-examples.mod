%% Binary resolution.  
module binary-examples.

accumulate control.
accumulate lkf-formulas, cforms, lkf-polarize.
accumulate lkf-kernel.
% accumulate lkf-hosted.
accumulate binary-fpc.
accumulate lists.
accumulate spy.

% All atoms are polarized positively.  (In the journal paper, this is
% the only thing we formally allow.)
polarize_pos A.  

test_all :- example N _ _ _,
  term_to_string N Str, print Str, print "  ", 
  test_resol' N, print "\n", fail.
test_resol' N :- (test_resol N, print "#", fail); true.

test_resol N :-
  example N Clauses Lemmas Resol, 
  foldl (C\A\R\ sigma D\sigma D'\ polarizeM (neg C) D, ensure+ D D', disj- A D' R) 
        Clauses f- B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (lkf_entry (start 1 Resol) B).

assume_lemmas C nil    G :- G.
assume_lemmas C [L|Ls] G :-
   C' is C + 1, polarizeM L L', ensure- L' L'',
%     term_to_string (lemma C L'') Str, print "Assuming ", print Str, print "\n",
   (lemma C L'' => assume_lemmas C' Ls G).

% The followineg are example certificates from the client's point-of-view.
% There are three lists:
%  1. The list of clauses, which when taken as hypothesis, yields
%     a contradiction. 
%  2. A list of "lemma".  These are new clauses that are resolvants
%     of previous clauses.
% 3. Sequence of triples describineg resolvants.

example 1 
  [a,
  (neg a)]
  [ff]
  [resol 1 2 3].

example 2 
  [(a or ff),
   ((neg a) or ff)]
  [ff]
  [resol 1 2 3].

example 3 
  [(r z),                            % 1
   (forall x\ (neg (r x)) or (t x)), % 2
   (neg (t z))]                      % 3
  [(t z),                            % 4
   ff]                               % 5
  [resol 1 2 4, resol 4 3 5].

example 4 
 [(r z),                                             % 1
  (forall x\ (neg (r x)) or (r (k x))),              % 2
  (neg (r (k (k (k (k z))))))]                       % 3
 [(forall x\ (neg (r x)) or (r (k (k x)))),          % 4
  (forall x\ (neg (r x)) or (r (k (k (k (k x)))))),  % 5
  (r (k (k (k (k z))))),                             % 6
  ff]                                                % 7
 [resol 2 2 4, resol 4 4 5, resol 1 5 6, resol 6 3 7].

example 5 
 [(r z),                                 % 1
  (forall x\ (neg (r x)) or (r (k x))),  % 2
  (neg (r (k (k (k (k z))))))]           % 3
 [(r (k z)),                             % 4
  (r (k (k z))),                         % 5
  (r (k (k (k z)))),                     % 6
  (r (k (k (k (k z))))),                 % 7
  ff]                                    % 8
 [resol 1 2 4, resol 4 2 5, resol 5 2 6, resol 6 2 7, resol 7 3 8].

example 6 
  [(a or a),
   ((neg a) or (neg a))]
  [ff]
  [resol 1 2 3].

example 7 
  [(a or b),            % 1
   ((neg a) or e),      % 2
   (neg b),             % 3
   (neg e)]             % 4
  [(b or e),            % 5
   e,                   % 6
   ff]                  % 7
  [resol 1 2 5, resol 5 3 6, resol 6 4 7].

example 8
  [(a or b),             % 1
   (a or (neg b)),       % 2
   ((neg a) or b),       % 3
   ((neg a) or (neg b))] % 4
  [(a or a),             % 5
   a,                    % 6
   ((neg a) or (neg a)), % 7
   (neg a),              % 8
   ff]                   % 9
  [resol 1 2 5, factor 5 6, resol 3 4 7, factor 7 8, resol 6 8 9].

example 9  % Just like 8 but factorineg is moved into the resol method
  [(a or b),             % 1
   (a or (neg b)),       % 2
   ((neg a) or b),       % 3
   ((neg a) or (neg b))] % 4
  [a,                    % 5
   (neg a),              % 6
   ff]                   % 7
  [resol 1 2 5, resol 3 4 6, resol 5 6 7].

example 10
  [(a or b),            % 1
   (a or (neg b)),      % 2
   (neg a)]             % 3
  [(a or a),            % 4
   a,                   % 5
   ff]                  % 6
  [resol 1 2 4, factor 4 5, resol 5 3 6].

example 11
  [(a or a),           % 1
   (neg a)]            % 2
  [a,                  % 3
   ff]                 % 4
  [factor 1 3, resol 3 2 4].

example 12 % dual of 11
  [((neg a) or (neg a)),    % 1
   a]                       % 2
  [(neg a),                 % 3
   ff]                      % 4
  [factor 1 3, resol 2 3 4].

example 13
  [a,                  % 1
   (neg a)]            % 2
  [ff]                 % 3
  [resol 1 2 3].

test 4 B :-
  example 4 Clauses Lemmas Resol, 
  foldl (C\A\R\ sigma D\sigma D'\ polarizeM (neg C) D, ensure+ D D', disj- A D' R) 
        Clauses f- B,
  length Clauses C, C' is C + 1,
  assume_lemmas C' Lemmas (spy (lkf_entry (start 1 Resol) B)).

