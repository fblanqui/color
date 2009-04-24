# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean default config dist doc install-dist install-doc tags

COQBIN ?= $(COQTOP)bin/
COQC := $(COQBIN)coqc
COQMAKE := $(MAKE) -f Makefile.coq

VFILES := $(shell find . -name '*.v')
VOFILES := $(VFILES:.v=.vo)
VCOMPILE := $(shell find . -name '*.v' -not -name 'Extraction.v')

all: extraction

default: Makefile.coq
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs"

extraction: ProofChecker/Extraction.vo
	

Makefile.coq:
	$(MAKE) config

config:
	coq_makefile -R . CoLoR $(VCOMPILE) > Makefile.coq
	$(COQMAKE) depend

clean:
	rm -f `find . -name \*~`
	rm -f doc/CoLoR.*.html doc/index.html
	rm -f -r certifiedCode
	$(COQMAKE) clean

tags:
	coqtags `find . -name \*.v`

doc:
	coqdoc --html -g -d doc -R . CoLoR `find . -name \*.v`
	./createIndex

./certifiedCode:
	mkdir certifiedCode

ProofChecker/Extraction.vo: ProofChecker/Extraction.v ProofChecker/ProofChecker.vo ./certifiedCode
	$(COQC) ProofChecker/Extraction.v
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
