module examples.
accumulate coc-ljf.
accumulate certificates/dd.

type f val.
type g val.
type h val.
type a val.
type b val.

% Examples dealing with sharing (ANF)
example 1 (app f (a ` a ` kappa _ x\ posbox x)).
example 2 (app f (a ` a ` kappa _ x\ app f (x ` x ` kappa _ y\ posbox y))).
example 3 (fun _ x\ posbox x).
example 4 (fun _ x\ app f (x ` x ` kappa _ y\ posbox y)).
example 5 (fun _ x\ app f (x ` x ` kappa _ y\ posbox x)).

% Examples dealing with copying (HNF)
example 11 (app b nl).
example 12 (app g ((negbox (app b nl)) ` (negbox (app b nl)) ` nl)).
example 13 (fun _ x\ app x nl).
example 14 (fun _ x\ app g ((negbox (app x nl)) ` (negbox (app x nl)) ` nl)).

% Examples mixing both normal forms

example 20 (app h (a ` (negbox (app b nl)) ` (kappa _ x\ posbox x))).
example 21 (fun _ x\ app h (x ` (negbox (app b nl)) ` (kappa _ y\ posbox y))).
example 22 (app h (a `
                  (negbox (app g ((negbox (app b nl)) `
                                  (negbox (app b nl)) ` nl))) `
                  (kappa _ x\ posbox x))).

% Higher-order examples

example 30 (fun _ u\ app u (a ` (kappa _ x\ posbox x))).
example 31 (fun _ u\ app f (a ` (kappa _ x\ posbox x))).
example 32 (fun _ u\ app u (a ` (kappa _ x\ app u (x ` (kappa _ y\ posbox y))))).

main :- 
  pi ky\ pi ty\ pi i\ pi o\ pi c5\ axiom (n ty) (n ky) => rel (n ty) (n ty) (n ty) => rel (n ky) (n ty) (n ty) =>
      sigma V\ sigma Ty\ sigma T\ sigma Ty2\
  % (syncr (dd 5) V Ty,
  % cut_vtt (sort (n ty)) (x \ fun (sort (n ty)) y \ fun (negbox (app y nl)) z \ app z nl) V, print V.
  % print "Generated" V,
  % (pi x\ store dd_index x Ty1 => asyncr (dd 3) (T x) (unk (Ty2 x))),
  % print "Generated" T,
  % cut_vtt V T R,
  % print Ty "e" Ty2,
  % cut_vvv Ty Ty2 Ty3,
  % print "Cioa" R "e" Ty3,
  % asyncr (dd 5) R (unk Ty3),
  % print "ok" Ty1 "against" Ty2 "Gives: \n" Ty3).
  cut_vvv (negbox (app c5 nl)) 
           (c11 \
 negbox
  (prod (negbox (app c3 nl)) (c12 \
    negbox
     (prod (negbox (prod (negbox (app c7 (negbox (app c11 nl) ` nl))) (c13 \ negbox (app c7 (negbox (app c12 nl) ` nl))) nl)) (c13 \
       negbox (app c7 (negbox (app c9 (negbox (app c11 nl) ` negbox (app c12 nl) ` nl)) ` nl))) nl)) nl)
           ) T, print T.