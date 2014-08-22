build: main.pdf
view: main.pdf ; xdg-open main.pdf 2>&1 > /dev/null

main.pdf: \
	section-intro.tex \
	section-background.tex \
	section-piware.tex \
	section-final.tex
	latexmk -pdf -f main.tex

section%.tex: section%.md ; pandoc $< -t beamer -o $@

clean: ; latexmk -C main.tex
veryclean: clean ; rm -f section*.tex

.PHONY: build clean veryclean
