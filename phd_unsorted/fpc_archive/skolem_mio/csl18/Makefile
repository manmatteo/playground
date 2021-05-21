main.pdf: main.tex
	pdflatex main
	bibtex main
#	perl ./fix-bib.pl main.bbl

bib: main.tex
	bibtex main
#	perl ./fix-bib.pl main.bbl

force: 
	pdflatex main
	bibtex main
#	perl ./fix-bib.pl main.bbl

show: main.pdf
	evince main.pdf&

clean:
	rm main.bbl main.blg main.log main.out main.vtc

#
# The following are specific to Dale's set up
# All others can ignore
#

dropbox: main.pdf
	cp main.pdf ~/Dropbox/Sync/Drafts/csl2018-draft.pdf

switch: 
	svn st
	svn commit -m "Switching machine."

publish: main.pdf
	cp main.pdf ~/www/papers/csl2018.pdf

zip: 
	zip chaudhuri-manighetti-miller.zip main.tex select.bib

html:
	cp skolem.html ~/Dropbox/Sync/Exports/
