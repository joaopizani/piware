
MAIN_NAME=main
REFERENCES_NAME=references
LATEXMKOPTS=-pdf -f -quiet
TEXT_PARTS_SRC=text

MAINTEX=$(TEXT_PARTS_SRC)/$(MAIN_NAME).tex
MAINPDF=./$(MAIN_NAME).pdf
REFERENCES=$(REFERENCES_NAME).bib
TEXT_PARTS=titlepage \
           abstract \
           chapter-introduction \
           chapter-background \
           chapter-piware \
           chapter-discussion-related-work \
           chapter-conclusions \
           acknowledgements


CODE_AGDA_ROOT=code/agda
CODE_AGDA_SRC=$(CODE_AGDA_ROOT)/src
CODE_AGDA_TRGLATEX=$(CODE_AGDA_ROOT)/latex
CODE_AGDA_STY=$(CODE_AGDA_TRGLATEX)/agda.sty
CODE_AGDA_STDLIB=${HOME}/build/agda/lib/current/src

CODE_AGDA_MODULES=Report/ChapterIntroduction \
                  Report/ChapterBackground \
                  Report/ChapterPiWare \
                  Data/CausalStream \
                  PiWare/Utils \
                  PiWare/Atom \
                  PiWare/Atom/Bool \
                  PiWare/Padding \
                  PiWare/Synthesizable \
                  PiWare/Synthesizable/Bool \
                  PiWare/Gates \
                  PiWare/Gates/BoolTrio \
                  PiWare/Circuit/Core \
                  PiWare/Circuit \
                  PiWare/Plugs/Core \
                  PiWare/Plugs \
                  PiWare/Simulation/Core \
                  PiWare/Simulation \
                  PiWare/Samples/BoolTrioComb \
                  PiWare/Samples/BoolTrioSeq \
                  PiWare/Patterns/Core \
                  PiWare/Patterns \
                  PiWare/Samples/RippleCarry \
                  PiWare/ProofSamples/BoolTrioComb \
                  PiWare/Samples/AndN \
                  PiWare/ProofSamples/AndN


all: $(MAINPDF)

$(MAINPDF): \
	$(CODE_AGDA_STY) \
	$(CODE_AGDA_MODULES:%=$(CODE_AGDA_TRGLATEX)/%.tex) \
	$(REFERENCES) \
	$(TEXT_PARTS:%=$(TEXT_PARTS_SRC)/%.tex)
	latexmk $(LATEXMKOPTS) $(MAINTEX)

$(CODE_AGDA_TRGLATEX)/%.tex: $(CODE_AGDA_SRC)/%.lagda
	mkdir -p "$(basename $@)"
	touch $@
	# agda -i $(CODE_AGDA_STDLIB) -i $(CODE_AGDA_SRC) --latex-dir=$(CODE_AGDA_TRGLATEX) --latex $<


clean:
	latexmk -c $(MAINTEX)

veryclean: clean
	rm -f $(CODE_AGDA_MODULES:%=$(CODE_AGDA_TRGLATEX)/%.tex)
	find $(CODE_AGDA_TRGLATEX) -type d -empty -delete
	rm -f $(MAINPDF)

.PHONY: clean veryclean all

