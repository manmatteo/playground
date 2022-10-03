module copy_interpreter.
accumulate classical.
accumulate lib.

flex T :- not (not (T = dummy)).
rigid T :- not (T = dummy).

% Flatten conjunctions of atoms to a list of atoms 
% flatten Body NewGoals
flatten (copyi X Y) [(copyi X Y)].
flatten (andq A B) NewGoals :- flatten A As, flatten B Bs, join As Bs NewGoals.

% instan Formula Instance
instan (allq B) C :- instan (B T) C.
instan (impq B C) (impq B C).
instan (andq B C) (andq B C).


% Main interpreter loop
% interp CopyAxioms CopyClauses Suspended Goals.

% Base case: no more goals, no suspended formulas
interp _ _ [] [].

% Restart on suspended formulas if no goals are present
interp Cs Gs Suspend [] :- interp Cs Gs [] Suspend.

% Solve the first goal using atomic copy definitions (could be incorporated into
% next case by replacing atoms with (impq true atom))
interp Cs Gs Su ((copyi T S) :: Goals) :-
       rigid T,
       memb (copyi T S) Cs,
       interp Cs Gs Su Cont.

% Solve the first goal using atomic copy definitions
interp Cs Gs Su ((copyi T S) :: Goals) :-
       rigid T,
       memb C Cs,
       instan C (impq Body (copyi T S)),
       flatten Body NewGoals,
       join NewGoals Goals Cont,
       interp Cs Gs Su Cont.

% The first goal is rigid and in the given atoms: continue with other goals
interp Cs Gs Su ((copyi T S) :: Goals) :-
       rigid T,
       memb (copyi T S) Gs,
       interp Cs Gs Su Goals.

% The first goal is flexible: add atom to suspend and continue with other goals
interp Cs Gs Su ((copyi T S) :: Goals) :-
       flex T,
       interp Cs Gs ((copyi T S) :: Su) Goals.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Test routines could be written in a better way: we are actually interested in
% inspecting the different solutions.

test_all :- example I Cs Gs Goal, 
            term_to_string I Str, print Str, print "  ", 
            test_spec Cs Gs Goal, print "\n", fail.

test_spec Cs Gs Goal :- (interp Cs Gs []  Goal, print "#", fail) ; true.

test I :- example I Cs Gs Goal, interp Cs Gs []  Goal.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% example N CopyClauses Atoms Goals

% This succeeds but is wildly non deterministic
example 1 [(copyi a a), allq x\ allq u\ (impq (copyi x u) (copyi (f x) (f u)))] [(copyi a b)]  [copyi (f (f a)) (f (f b))].

% This succeeds but is actually only finding the first solution X = f (f a).
% The solution X = f (f b) is not reached possibly because of the same issue as above
example 2 [(copyi a a), allq x\ allq u\ (impq (copyi x u) (copyi (f x) (f u)))] [(copyi a b)]  [copyi (f (f a)) X].
