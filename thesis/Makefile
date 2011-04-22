clean:
	rm *.aux *.bbl *.blg *.log *.pdf 

thesis: 
	svn commit -m 'making version for upload' 
	svn info thesis.tex -r HEAD | grep Revision > version.txt
	pdflatex thesis.tex
	bibtex thesis
	pdflatex thesis
	pdflatex thesis
	scp thesis.pdf neelk@linux.gp.cs.cmu.edu:/afs/cs/users/neelk/www/thesis.pdf

