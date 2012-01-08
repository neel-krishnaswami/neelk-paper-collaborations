all: thesis

clean:
	rm *.aux *.bbl *.blg *.log *.pdf 

.PHONY: all clean upload

thesis: 
	pdflatex thesis.tex
	bibtex thesis
	pdflatex thesis
	pdflatex thesis

upload: thesis
	svn info thesis.tex -r HEAD | grep Revision > version.txt
	svn commit -m 'making version for upload' 
	scp thesis.pdf neelk@linux.gp.cs.cmu.edu:/afs/cs/user/neelk/www/thesis.pdf

