# Makefile for the imbedding

TJROOT = /home/matteo/software/teyjus
#VPATH = ../common

#export TJPATH = ../common

.PHONY: all 
all: basic lkf exptrees geo ginterp max

.PHONY: basic
basic: lib.lp

.PHONY: lkf 
lkf: basic classical.lp lkf-formulas.lp lkf-kernel.lp 

.PHONY: exptrees
exptrees: lkf exp-fpc.lp exp-examples.lp

.PHONY: exp-sk
exptrees: lkf exp-sk-fpc.lp exp-examples.lp

.PHONY: max
exptrees: lkf maxcert.lp skolem-lk-examples.lp

.PHONY: geo
geo: lkf geo-fpc.lp geo-examples.lp

.PHONY: ginterp
ginterp: basic ginterp.lp classical.lp

%.lpo : %.mod %.sig
	$(TJROOT)/tjcc  $*

%.lp : %.lpo
	$(TJROOT)/tjlink  $*

-include depend
depend: *.mod *.sig
		$(TJROOT)/tjdepend *.mod  > depend-stage
		mv depend-stage depend

.PHONY: clean
clean:
	rm -f *.lpo *.lp *.DT depend

.PHONY: tests
tests: geo-examples.lp
	$(TJROOT)/tjsim -b -s "test_all." exp-examples.
