build: main.pdf
view: main.pdf ; xdg-open main.pdf 2>&1 > /dev/null

main.pdf: main.tex agda/latex/agda.sty \
	section-intro-background.tex \
	section-dtp-agda.tex \
	section-piware.tex \
	section-final.tex
	latexmk -pdf -f -quiet main.tex

section%.tex: section%.md ; pandoc $< -t beamer -o $@

clean: ; latexmk -c main.tex
veryclean: clean ; rm -f section*.tex main.pdf

.PHONY: build clean veryclean
