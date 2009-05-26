# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean default config dist doc install-dist install-doc tags extraction

COQC := $(COQBIN)coqc

COQMAKE := $(MAKE) -f Makefile.coq

EXT_VFILES := ProofChecker/Extraction.v ProofChecker/ProofChecker.v

VFILES := $(shell find . -name '*.v' -not -name Extraction.v -not -name ProofChecker.v)

default: Makefile.coq
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs"

extraction: Makefile.ext ProofChecker/Extraction.vo

Makefile.ext:
	coq_makefile -R . CoLoR $(VFILES) $(EXT_VFILES) > Makefile.ext
	$(MAKE) -f Makefile.ext depend

Makefile.coq:
	$(MAKE) config

config:
	coq_makefile -R . CoLoR $(VFILES) > Makefile.coq
	$(COQMAKE) depend

clean:
	$(COQMAKE) clean
	rm -f `find . -name \*~`
	rm -f doc/CoLoR.*.html doc/index.html
	rm -f -r certifiedCode

tags:
	coqtags `find . -name \*.v`

doc:
	coqdoc --html -g -d doc -R . CoLoR `find . -name \*.v`
	./createIndex

./certifiedCode:
	mkdir -p certifiedCode

ProofChecker/Extraction.vo: ./certifiedCode
	$(MAKE) -f Makefile.ext $@
	mv *.ml* ./certifiedCode

ADR := login-linux.inria.fr:liama/www/color

install-doc:
	scp doc/coqdoc.css doc/*.html $(ADR)/doc

dist:
	./createDist

install-dist:
	scp CoLoR_`date +%y%m%d`.tar.gz $(ADR)/CoLoR.tar.gz
	scp CHANGES $(ADR)/CHANGES.CoLoR

%.vo: %.v
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs" $@

%:
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs" $@
