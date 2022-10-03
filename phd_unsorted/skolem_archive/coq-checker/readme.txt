		    ==============================
		    === Intuitionistic checker ===
		    ==============================
iforms.sig
  Use these constants to encode intuitionistic logic (unpolarized)

ljf-formulas.sig
ljf-formulas.mod
  Syntax and utilities for the kernel,	internal, intuitionistic logic.

ljf-polarize.mod
ljf-polarize.sig

ljf-certificates.sig
  The API for the clerks and experts.  These predicates are called by
  the kernel and are defined by the C&Es.

ljf-kernel.sig
ljf-kernel.mod

stlc-examples.mod
stlc-examples.sig
stlc-fpc.mod
stlc-fpc.sig

mimic-examples.mod
mimic-examples.sig
mimic-fpc.mod
mimic-fpc.sig

jhc-examples.mod - Justified Horn clauses certificates
jhc-examples.sig
jhc-fpc.mod
jhc-fpc.sig

deb-examples.mod
deb-examples.sig
deb-fpc.mod
deb-fpc.sig
		      =========================
		      === Classical checker ===
		      =========================

cforms.sig
  Use these constants to encode intuitionistic logic (unpolarized)

lkf-formulas.sig
lkf-formulas.mod
  Syntax and utilities for the kernal, internal, classical logic.

lkf-polarize.mod
lkf-polarize.sig

lkf-certificates.sig
  The API for the clerks and experts.  These predicates are called by
  the kernel and are defined by the C&Es.

lkf-kernel.sig
lkf-kernel.mod

lkf-hosted.sig
lkf-hosted.mod

cnf-fpc.sig
cnf-fpc.mod
cnf-examples.sig 
cnf-examples.mod

oracle-fpc.sig
oracle-fpc.mod
oracle-examples.sig 
oracle-examples.mod

binary-fpc.sig
binary-fpc.mod
binary-examples.sig 
binary-examples.mod

			 ===================
			 ===  Utilities  ===
			 ===================
contol.mod
contol.sig
lists.mod
lists.sig
spy.mod
spy.sig

	  =================================================
	  ====  Description of the preambles of files  ====
	  =================================================
sig xyz-fpc.
accum_sig ljf-certificates.


module xyz-fpc.


sig xyz-examples.
accum_sig lkf-kernel, lkf-polarize.
accum_sig xyz-fpc.


module xyz-examples.
accumulate lkf-formulas, cforms, lkf-polarize.
accumulate lkf-kernel.
accumulate xyz-fpc.

			======================
			===  Dependencies  ===
			======================

      cforms              lkf_formulas
        |                /     |
        |     -----------      |
        |    /                 |
  lkf_polarize        lkf-certificates.sig
        \                |
         \               |
          \        lkf-kernel
           \         |
            \       fpc
             \      |
              \    /
              examples


   ================================================================
			       Clients
   ================================================================


The client-side and kernel-side terms are the same (we probably need
to adjust this when dealing with skolemization).

We provide them with generic constructors for classical and
intuitionistic logics.
  iforms.* cforms.*

We also provide common polarization predicates for both classical and
intuitionistic logics.  These predicates do the translation of
client-side to kernel-side formulas.



