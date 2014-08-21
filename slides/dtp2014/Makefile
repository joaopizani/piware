build: main.pdf

view: main.pdf ; xdg-open main.pdf 2>&1 > /dev/null

main.pdf: section1.tex section2.tex section3.tex ; latexmk -pdf -f main.tex

section%.tex: section%.md ; pandoc $< -t beamer -o $@

clean: ; latexmk -C main.tex

veryclean: clean ; rm -f section*.tex

.PHONY: build clean veryclean
