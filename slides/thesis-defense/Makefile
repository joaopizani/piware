build: main.pdf
view: main.pdf ; xdg-open main.pdf 2>&1 > /dev/null

main.pdf: \
	agda/latex/agda.sty \
	agda/latex/Defense/SectionDTPAgda.tex \
	agda/latex/PiWare/Circuit/Core.tex \
	agda/latex/PiWare/Circuit.tex \
	agda/latex/PiWare/Atom.tex \
	agda/latex/PiWare/Atom/Bool.tex \
	agda/latex/PiWare/Gates.tex \
	agda/latex/PiWare/Gates/BoolTrio.tex \
	agda/latex/PiWare/Synthesizable.tex \
	agda/latex/PiWare/Simulation/Core.tex \
	agda/latex/PiWare/Simulation.tex \
	agda/latex/PiWare/Samples/BoolTrioComb.tex \
	agda/latex/PiWare/Samples/BoolTrioSeq.tex \
	agda/latex/PiWare/ProofSamples/BoolTrioComb.tex \
	agda/latex/PiWare/ProofSamples/BoolTrioSeq.tex \
	agda/latex/PiWare/Samples/AndN.tex \
	agda/latex/PiWare/ProofSamples/AndN.tex \
	main.tex \
	section-intro-background.tex \
	section-dtp-agda.tex \
	section-piware-syntax.tex \
	section-piware-semantics.tex \
	section-piware-proofs.tex \
	section-final.tex
	patch -p0 < section-final.patch
	latexmk -pdf -f -quiet main.tex

section%.tex: section%.md ; pandoc $< -t beamer -o $@

clean: ; latexmk -c main.tex
veryclean: clean ; rm -f section*.tex main.pdf

.PHONY: build clean veryclean
