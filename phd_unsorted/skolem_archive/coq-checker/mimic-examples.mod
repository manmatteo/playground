module mimic-examples.
accumulate control.
accumulate ljf-formulas, iforms, ljf-polarize.
accumulate ljf-kernel.
accumulate lists.
accumulate mimic-fpc.

trans tt t-.
trans ff f.
trans (T imp S) (A arr B) &
trans (T and S) (A &-& B) &
trans (T or  S) (A !+!  B) :- trans T A, trans S B.
trans a (p a)  &  trans b (p b)  &  trans c (p c) &  trans d (p d).
trans (q X) (p (q X)). 
trans (r X) (p (r X)). 

trans (forall T) (all A) :- pi x\ trans (T x) (A x).
trans (exists T) (some A) :- pi x\ trans (T x) (A x).

check_cert IForm :- 
  trans IForm Form, (d+ Form) = Form', 
  ljf_entry (mimic root) (Form' arr Form').

test I :- example I IForm, check_cert IForm.

test_all :- 
   example X IForm,
   (sigma Str\ term_to_string X Str, print Str, print " "),
   if (check_cert IForm)
      (print "Success\n") 
      (print "Fail\n"), 
  fail.

type check_two iform -> iform -> prop.
check_two A B :- 
  trans A FormA, (d+ FormA) = FormA',
  trans B FormB, (d+ FormB) = FormB',
  ljf_entry (mimic root) (FormA' arr FormB').


example 1 (a and b).
example 2 (a and b and c).
example 3 (a or b or c).
example 4 (a or (b imp c)).
example 5 (a imp b).
example 6 (a imp b imp c).
example 7 ((a imp b) imp c).
example 8 (((a and (b or c)) imp (b or c)) imp c).
example 9 tt.
example 10 ff.
example 11 a.

%% 12->13 è provabile! Molto strano!
example 12 (exists x\ ((q x) and (r x)) ).
example 13 ((exists x\ (q x)) and (forall x\ (r x)) ).

example 14 (exists x\ (q x)).

%% Di questo non riesco a provare A->A !!
example 15 (forall x\ (q x)).

example 16 (exists x\ ((q x) or (r x))).
example 17 ((exists x\ (q x)) or (exists x\ (r x))).


type mini int -> iform -> prop.
mini 1 ((exists x\ ((q x) and (r x)) )
     imp ((exists x\ (q x)) and (exists x\ (r x)))).

mini 2 ((forall x\ ((q x) and (r x)) )
     imp ((forall x\ (q x)) and (forall x\ (r x)))).

mini 3 ((exists x\ ((q x) and a ))
     imp ((exists x\ (q x)) and a)).

mini 4 ((exists x\ ((q x) or a ))
     imp ((exists x\ (q x)) or a)).

mini 5 ((forall x\ ((q x) or a ))
     imp ((forall x\ (q x)) or a)).

mini 6 ((forall x\ ((q x) and a ))
     imp ((forall x\ (q x)) and a)).

mini 7 ((exists x\ ((q x) or (r x)) )
     imp ((exists x\ (q x)) or (exists x\ (r x)))).

mini 8 ((forall x\ ((q x) or a ))
     imp ((forall x\ (q x)) or a)).


type check_mini int -> prop.
check_mini N :- 
  mini N Form, trans Form Form',
  ljf_entry (mimic root) Form'.
