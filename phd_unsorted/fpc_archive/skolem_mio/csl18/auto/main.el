(TeX-add-style-hook
 "main"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("lipics-v2018" "a4paper" "USenglish")))
   (TeX-run-style-hooks
    "latex2e"
    "lipics-v2018"
    "lipics-v201810"
    "skolem")
   (TeX-add-symbols
    "sksig"
    "lkfruleshere"
    "lkfaruleshere")
   (LaTeX-add-labels
    "sec:intro"
    "ssec:advantages"
    "ssec:deskolem"
    "sec:skolemization"
    "sec:seq"
    "fig:lkf-rules"
    "sec:fpc"
    "fig:lkfa-rules"
    "sec:deskolem"
    "sec:implementation"
    "fig:exp-cert"
    "fig:exp-fpc"
    "sec:related")
   (LaTeX-add-bibliographies
    "/home/matteo/repo/parsifal/papers/references/master")))

