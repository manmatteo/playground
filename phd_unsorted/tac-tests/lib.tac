%%Title: nat.thm
%%Description: Some definitions and theorems about the most basic
%%             aspects of nature numbers
%%Author: Dale Miller
%%Dates: 6 March 2017, 31 December 2018
%%Ported to Tac: Matteo Manighetti, 31 January 2019

#define "nat {x} := (x=o);(sigma y\ (x=(s y),(nat y)))".
#define "even {x} := (x=o);(sigma y\ (x=(s (s y)),(even y)))".
#define "odd {x} := (x=(s o));(sigma y\ (x=(s (s y)),(odd y)))".

#theorem even_or_even_s "pi x\ nat x => even x ; even (s x)".
prove.
#theorem onono "pi N\ nat N => (N = o ; sigma M\ nat M , N = (s M))".
prove.
#theorem nat_s "pi N\ nat N => nat (s N)".
prove.
#theorem s_nat "pi N\ nat (s N) => nat N".
prove.
#theorem eq_o_decidable "pi n\ nat n => ((n = o => false) ; (n = o))".
prove.
#theorem decideeq "pi N\ nat N => pi M\ nat M => ((N = M => false) ; (N = M))".
prove.
#theorem even_type "pi X\ even X => nat X".
prove.
#theorem odd_type "pi X\ odd X => nat X".
prove.
#theorem even_odd "pi N\ even N => odd (s N)".
prove.
#theorem odd_even "pi N\ odd N => even (s N)".
prove.
#theorem even_or_odd "pi N\ nat N => even N ; odd N".
prove.
#theorem not_odd_even "pi X\ nat X => (odd X => false) => even X".
prove.
#theorem even_odd_exclusion "pi N\ even N => odd N => false".
prove.
%%Title: nat-order.thm
%%Description: Some definitions and theorems about ordering 
%%             on nature numbers
%%Author: Dale Miller
%%Dates: 4 January 2019

%include "http://www.lix.polytechnique.fr/Labo/Dale.Miller/alib/nat.thm".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%    Greater and lessthan relationship on nat            %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

#define "greater {x} y := (x=s y);(sigma p\ (x=(s p),(greater p y)))".
#define "lesseq x {y} := (x=y);(sigma z\ (y=(s z),(lesseq x z)))".
#define "less x {y} := (s x = y);(sigma z\ (y=(s z),(less x z)))".
#theorem greater_less "pi N\ M\ greater N M => less M N".
prove.
#theorem less_greater "pi N\ M\ less N M => greater M N".
prove.
#theorem simple_less "pi N\ nat N => less N (s N)".
prove.
#theorem s_greater "pi N\ nat N => greater (s N) N".
prove.
#theorem greater_greater "pi N\ M\ nat M => greater N (s M) => greater N M".
prove.
#theorem greater_s "pi N\ M\ nat N => nat M => greater N M => N = (s M) ; greater N (s M)".
prove.
#theorem less_s "pi N\ M\ nat N => nat M => less N M => (s N) = M ; less (s N) M".
prove.
#theorem greater_s1 "pi N\ M\ greater N M => greater (s N) M".
prove.
#theorem trichotomy "pi N\ nat N => pi M\ nat M => (greater N M ; N = M ; less N M)".
prove.
#theorem trichotomyA "pi N\ M\ nat N => nat M => less N M => N = M => false".
prove.
#theorem trichotomyB "pi N\ M\ nat N => nat M => less N M => greater N M => false".
prove.
#theorem trichotomyC "pi N\ M\ nat N => nat M => greater N M => N = M => false".
prove.
#theorem simple_three "pi N\ less N (s (s o)) => N = o ; N = (s o) ; N = (s (s o))".
prove.
#theorem lesseq_less "pi N\ M\ lesseq N M => N = M ; less N M".
prove.
#theorem lesseq_eq "pi N\ nat N => lesseq N N".
prove.
#theorem lesseq_trans "pi N\ M\ P\ lesseq N M => lesseq M P => lesseq N P".
prove.
#theorem lesseq_type "pi N\ M\ lesseq N M => nat N".
prove.
#theorem lesseq_s "pi N\ M\ lesseq N M => lesseq N (s M)".
prove.
#theorem lesseq_anitsym "pi N\ M\ lesseq N M => lesseq M N => N = M".
prove.

%%Title: plus.thm
%%Description: Addition on nature numbers
%%Author: Dale Miller
%%Dates: 4 January 2019

%include "http://www.lix.polytechnique.fr/Labo/Dale.Miller/alib/nat.thm".

#define "plus {x} y z := (y=z,x=o);(sigma m\n\ (x=(s m), z=(s n), (plus m y n)))".
% Typing judgments for plus
#theorem augend_nat "pi A\ B\ C\ plus A B C => nat B => nat C => nat A".
prove.
#theorem augend_nat1 "pi A\ B\ C\ plus A B C => nat C => nat A".
prove.
#theorem addend_nat "pi A\ B\ C\ plus A B C => nat C => nat B".
prove.
#theorem plus_nat "pi A\ B\ C\ plus A B C => nat A => nat B => nat C".
prove.
#theorem plus_type1 "pi N\ M\ P\ plus N M P => nat N".
prove.
#theorem plus_type2 "pi N\ M\ P\ nat M => plus N M P => nat P".
prove.
#theorem plus_oero "pi N\ nat N => plus N o N".
prove.
#theorem plus_s "pi M\ N\ K\ plus M N K => plus M (s N) (s K)".
prove.
#theorem plus_comm "pi M\ N\ K\ nat K => plus M N K => plus N M K".
prove.
#theorem plus_det "pi A\ B\ C\ D\ plus A B C => plus A B D => C = D".
prove.
#theorem plus_assoc "pi A\ B\ C\ AB\ ABC\ plus A B AB => plus AB C ABC => sigma BC\ plus B C BC, plus A BC ABC".
prove.
#theorem plus_assoc_rl "pi A\ B\ C\ BC\ ABC\ nat ABC => plus B C BC => plus A BC ABC => sigma AB\ plus A B AB, plus AB C ABC".
prove.
#theorem plus_perm4 "pi A\ B\ C\ D\ AB\ CD\ ABCD\ nat ABCD => plus A B AB => plus C D CD => plus AB CD ABCD => sigma AC\ BD\ plus A C AC, plus B D BD, plus AC BD ABCD".
prove.
#theorem plus_total "pi M\ N\ nat M => sigma K\ plus M N K".
prove.
#theorem plus_total1 "pi M\ N\ nat M => nat N => sigma K\ nat K, plus M N K".
prove.
#theorem plus_swaprl "pi A\ B\ C\ plus A (s B) C => plus (s A) B C".
prove.
#theorem plus_swaplr "pi A\ B\ C\ plus (s A) B C => plus A (s B) C".
prove.
#theorem plus_one "pi N\ nat N => plus N (s o) (s N)".
prove.
#theorem plus_twice "pi N\ M\ nat N => plus N N M => even M".
prove.
#theorem odd_plus_even "pi X\ Y\ Z\ odd X => even Y => plus X Y Z => odd Z".
prove.
#theorem odd_plus_odd "pi X\ Y\ Z\ odd X => odd Y => plus X Y Z => even Z".
prove.

%%Title: times.thm
%%Description: Multiplication on nature numbers
%%Author: Dale Miller, based on a develop from Rob Blanco
%%Dates: 4 January 2019

%include "http://www.lix.polytechnique.fr/Labo/Dale.Miller/alib/nat.thm".
%include "http://www.lix.polytechnique.fr/Labo/Dale.Miller/alib/plus.thm".

#define "times {x} y z := (x=0,y=0);(sigma k\ n1\ (x = s k),times k m n1, plus n1 m n)".
#theorem times_nat "pi A\ B\ C\ times A B C => nat A => nat B => nat C".
prove.
#theorem times_oero "pi N\ nat N => times N o o".
prove.
#theorem times_total1 "pi M\ N\ nat M => nat N => sigma K\ nat K , times M N K".
prove.
#theorem times_det "pi A\ B\ C\ D\ times A B C => times A B D => C = D".
prove.
#theorem times_one "pi N\ nat N => times N (s o) N".
prove.
#theorem times_one_simpl "pi A\ B\ times (s o) A B => A = B".
prove.
#theorem times_s "pi M\ N\ MN\ nat M => nat N => nat MN => times M N MN => sigma K\ nat K,plus MN M K,times M (s N) K".
prove.
#theorem times_incr "pi A\ B\ AB\ ABB\ nat ABB => times A B AB => plus AB B ABB => times (s A) B ABB".
prove.
% In reverse
#theorem times_sl "pi A\ B\ C\ nat A => nat B => nat C => times A B C => exists D, nat D , times (s A) B D , plus C B D".
prove.
% Commutativity of multiplication %
#theorem times_comm "pi M\ N\ K\ nat M => nat N => nat K => times M N K => times N M K".
prove.
% Distributivity of multiplication over addition %
% A constructive version
#theorem distribute "pi X\ Y\ ZERO\ YpZERO\ T\
 	nat X => nat Y => nat ZERO => nat YpZERO => nat T =>
 	plus Y ZERO YpZERO => times X YpZERO T =>
 	sigma XtY\ XtZERO\
 	nat XtY , nat XtZERO ,
 	times X Y XtY , times X ZERO XtZERO , plus XtY XtZERO T".
prove.
% % In reverse
#theorem undistr_times_plus "pi X\ Y\ ZERO\ XtY\ XtZERO\ XtYpXtZERO\
	nat X => nat Y => nat ZERO =>
	nat XtY => nat XtZERO => nat XtYpXtZERO =>
	times X Y XtY => times X ZERO XtZERO => plus XtY XtZERO XtYpXtZERO =>
	sigma YpZERO\ XtYpZERO\
	nat YpZERO , nat XtYpZERO ,
	times Y ZERO YpZERO , times X YpZERO XtYpZERO".
prove.
% Associativity of multiplication %
#theorem times_assoc "pi A\ B\ C\ AB\ ABC\ nat A => nat B => nat C => nat AB => nat ABC => times A B AB => times AB C ABC => sigma BC\ times B C BC , times A BC ABC".
prove.
#theorem times_incr "pi A\ B\ AB\ ABB\ nat ABB => times A B AB => plus AB B ABB => times (s A) B ABB".
prove.
#theorem times_sl "pi A\ B\ C\ nat A => nat B => nat C => times A B C => sigma D\ nat D, times (s A) B D, plus C B D".
prove.
#theorem times_comm1 "pi M\ N\ K\ nat M => nat N => nat K => times M N K => times N M K".
prove.
#theorem distribute "pi X\ Y\ ZERO\ YpZERO\ T\ nat X => nat Y => nat ZERO => nat YpZERO => nat T => plus Y ZERO YpZERO => times X YpZERO T => sigma XtY\ XtZERO\ nat XtY, nat XtZERO, times X Y XtY, times X ZERO XtZERO, plus XtY XtZERO T".
prove.
#theorem undistr_times_plus "pi X\ Y\ ZERO\ XtY\ XtZERO\ XtYpXtZERO\ nat X => nat Y => nat ZERO => nat XtY => nat XtZERO => nat XtYpXtZERO => times X Y XtY => times X ZERO XtZERO => plus XtY XtZERO XtYpXtZERO => sigma YpZERO\ XtYpZERO\ nat YpZERO, nat XtYpZERO, times Y ZERO YpZERO, times X YpZERO XtYpZERO".
prove.
#theorem times_assoc1 "pi A\ B\ C\ AB\ ABC\
	nat A => nat B => nat C => nat AB => nat ABC =>
	times A B AB => times AB C ABC => sigma BC\ times B C BC, times A BC ABC".
prove.
#theorem times2_even "pi X\ Y\ nat X => times (s (s o)) X Y => even Y".
prove.
#theorem even_times2 "pi Y\ even Y => sigma Y1\ times (s (s o)) Y1 Y".
prove.
#theorem odd_times_odd "pi X\ Y\ Z\ odd X => odd Y => times X Y Z => odd Z".
prove.
#define "square {x} y := times x x y".
#theorem temp "pi N\ S\ nat N => square N S => even S => even N".
prove.
%%Title: monotone.thm
%%Description: Relating addition and order relation on nature numbers
%%Author: Dale Miller
%%Dates: 4 January 2019

%include "http://www.lix.polytechnique.fr/Labo/Dale.Miller/alib/nat.thm".
%include "http://www.lix.polytechnique.fr/Labo/Dale.Miller/alib/nat-order.thm".
%include "http://www.lix.polytechnique.fr/Labo/Dale.Miller/alib/plus.thm".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%    Relate plus and order                               %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

#theorem plus_monotone "pi N\ M\ P\ greater M o => plus N M P => greater P N".
prove.
#theorem plus_monotone1 "pi N\ M\ I\ P\ Q\ greater M I => plus N I P => plus N M Q => greater Q P".
prove.
#theorem monotone_plus0 "pi N\ M\ P\ nat M => plus N M P => lesseq M P".
prove.

%%Title: fibonacci.thm
%%Description: Some simple theorems about the Fibonacci series.
%%Author: Dale Miller
%%Dates: 25 October 2016, 4 January 2019

%include "http://www.lix.polytechnique.fr/Labo/Dale.Miller/alib/nat.thm".
%include "http://www.lix.polytechnique.fr/Labo/Dale.Miller/alib/nat-order.thm".
%include "http://www.lix.polytechnique.fr/Labo/Dale.Miller/alib/plus.thm".
%include "http://www.lix.polytechnique.fr/Labo/Dale.Miller/alib/times.thm".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%    Fibonacci numbers     (DM 25 Oct 2016)              %%%%
%%%%                                                        %%%%
%%%%    The main theorem proved below is that (fib N) = N   %%%%
%%%%    if and only if N is a member of the set {0, 1, 5}.  %%%%
%%%%                                                        %%%%
%%%%    There is a similar theorem not yet attempted:       %%%%
%%%%    (fib N) = N*N if and only if N is a member of the   %%%%
%%%%    set {0, 1, 12}.                                     %%%%
%%%%                                                        %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
#define "fib {x} y := (x=o,y=o);(x=s o,y=s o);(sigma N\F1\F2\F\ x = s s N, fib N F1, fib (s N) F2, plus F1 F2 F)".
#theorem fib_three "pi F\ fib (s (s (s o))) F => F = (s (s o))".
prove.
#theorem fib_four "pi F\ fib (s (s (s (s o)))) F => F = (s (s (s o)))".
prove.
%% #theorem fib_five "pi F\ fib (s (s (s (s (s o))))) F => F = (s (s (s (s (s o)))))".
%% #theorem fib_six "pi F\ fib (s (s (s (s (s (s o)))))) F =".
%% #theorem fib_seven "pi F\ fib (s (s (s (s (s (s (s o))))))) F =>".
#theorem fib_det "pi A\ B\ C\ nat A => nat B => nat C => fib A B => fib A C => B = C".
prove.
#theorem fib_type "pi N\ nat N => (pi F\ fib N F => nat F) , (pi F\ fib (s N) F => nat F)".
prove.
% There are at least three solutions to the fibonacci equation (fib N) = N.
#theorem three_solutions "pi N\ (N = o ; N = (s o) ; N = (s (s (s (s (s o)))))) => fib N N".
prove.
% The converse of this theorem takes a bit more work
%% Strange problem: "prove" loops!
% #theorem plus_greater "pi X\ Y\ W\ N\ nat N => nat X => nat Y => greater X N => greater Y (s N) => plus X Y W => greater W (s (s N))".
% prove.
#theorem fib_bounding "pi N\ nat N => (pi F\ (fib (s (s (s (s (s (s N)))))) F => greater F (s (s (s (s (s (s N)))))))), (pi F\ (fib (s (s (s (s (s (s (s N))))))) F => greater F (s (s (s (s (s (s (s N)))))))))".
prove.
#theorem only_three_solutions "pi N\ nat N => fib N N => (N = o ; N = (s o) ; N = (s (s (s (s (s o))))))".
prove.
%% The following is yet to be proved (in Abella. Here it is proved!)
#theorem bounded "pi N\ F\ Sq\ nat N => less (s (s (s (s (s (s (s (s (s (s (s (s o)))))))))))) N => fib N F => times N N Sq => less Sq F".
prove.
