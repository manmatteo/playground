module binary-fpc.
/* start */
orNeg_kc (start C Resol) (start C Resol).
false_kc (start C Resol) (start C Resol).
store_kc (start C Resol) (start D Resol) (idx C) :- D is C + 1.
/* end */

/* cut */
cut_ke (start C Resol) C1 C2 Cut :- cut_ke (rlist Resol) C1 C2 Cut.
cut_ke (rlist (resol I J K::Rs)) (dlist [I,J]) (rlisti K Rs) Cut :-
  lemma K Cut.
store_kc  (rlisti K Rs) (rlist Rs) (idx K).
decide_ke (rlist []) rdone (idx I).
true_ke   rdone.
/* end */

/* dlist */
all_kc     (dlist L) (x\ dlist L) & orNeg_kc (dlist L) (dlist L).
false_kc   (dlist L) (dlist L) & store_kc (dlist L) (dlist L) lit.
decide_ke  (dlist L) (dlist [J]) (idx I) :- L = [I,J] ; L = [J,I].
decide_ke  (dlist [I]) (dlist []) (idx I).
decide_ke  (dlist L) (dlist []) lit :- L = [I]; L = [].
initial_ke (dlist L) lit.
true_ke    (dlist L).
andPos_ke  (dlist L) (dlist L) (dlist L).
some_ke    (dlist L) (dlist L) T.
release_ke (dlist L) (dlist L).
/* end */

/* factor */
cut_ke (rlist (factor I K ::Rs)) (factr I) (rlisti K Rs) Cut :-
  lemma K Cut.
all_kc     (factr I) (x\ factr I).
orNeg_kc   (factr I) (factr I) & store_kc (factr I) (factr I) lit.
false_kc   (factr I) (factr I) & decide_ke (factr I) fdone (idx I).
true_ke    fdone               & andPos_ke fdone fdone fdone.
some_ke    fdone fdone T       & decide_ke fdone fdone lit.
release_ke fdone fdone         & store_kc  fdone fdone lit.
initial_ke fdone lit.
/* end */



% DM Tasks:
% (1) The resol method allows factoring.   Consider adding a method 
%     that does not do factoring.  This changes backtracking / performance?
% (2) Examples 8 and 9 have excessive backtracking.  Understand this.

% Note: if we require the first clause in a resolution triple to be
%  the clause with the "postive" resolving literal, then some of
%  non-determinism in checking is eliminated.  See (*) in comment
%  below.  This suggests a different proof certificate format where
%  the user is requested to make such a choice.  This is likely to be
%  a recurring theme: there is a lot of non-determinism in checking
%  proofs: the checker can search to resolve it or the user can do
%  some additional work to help remove some worthless non-determinism.

