
STDLIB=${HOME}/build/agda/lib/current/src
TRG=../latex


all: $(TRG)/Report/ChapterIntroduction.tex $(TRG)/Report/ChapterBackground.tex

$(TRG)/%.tex: ./%.lagda
	agda -i $(STDLIB) -i . --latex-dir=$(TRG) --latex $<

.PHONY: clean

clean:
	find $(TRG) ! -name agda.sty -delete
