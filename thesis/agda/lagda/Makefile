
STDLIB=${HOME}/build/agda/lib/current/src
TRG=../latex


all: $(TRG)/Report/Chapter1.tex

$(TRG)/%.tex: ./%.lagda
	agda -i $(STDLIB) -i . --latex-dir=$(TRG) --latex $<

.PHONY: clean

clean:
	find $(TRG) ! -name agda.sty -delete
