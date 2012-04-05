all: thesis

clean:
	rm *.aux *.bbl *.blg *.log *.pdf 

.PHONY: all clean upload version

thesis: 
	pdflatex thesis.tex
	bibtex thesis
	pdflatex thesis
	pdflatex thesis

version:
	svn info thesis.tex -r HEAD | grep Revision > version.txt

upload: version thesis
	svn commit -m 'making version for upload' 
	scp thesis.pdf neelk@linux.gp.cs.cmu.edu:/afs/cs/user/neelk/www/thesis.pdf
	cp thesis.pdf /www/sws-homepage/neelk/thesis.pdf

