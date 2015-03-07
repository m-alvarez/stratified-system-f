all: report.pdf

%.pdf: %.tex
	pdflatex $< && pdflatex $<

clean:
	rm *.aux *.log *.pdf
