COQC=coqc

DN= dn_term.v dn_context.v dn_red.v dn_typ.v dn_sr.v
DNO= $(DN:.v=.vo)

SC = sc_term.v sc_context.v sc_red.v sc_typ.v sc_sr.v
SCO= $(SC:.v=.vo)


all: dn sc equiv.vo

sc : dn ${SCO}
dn : ${DNO}

%.vo: %.v
	${COQC} $^



clean:
	rm -f *.vo *.glob
