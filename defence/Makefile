all: defence.pdf

defence.pdf: defence.tex
	pdflatex -shell-escape defence.tex && pdflatex -shell-escape defence.tex

clean:
	rm defence.pdf *.aux *.log
