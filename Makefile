# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean default config dist doc install-dist install-doc tags

COQMAKE := $(MAKE) -f Makefile.coq

default: Makefile.coq
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs"

Makefile.coq:
	$(MAKE) config

config:
	coq_makefile -R . CoLoR `find . -name \*.v` > Makefile.coq
	$(COQMAKE) depend

clean:
	rm -f `find . -name \*~`
	rm -f doc/CoLoR.*.html doc/index.html
	$(COQMAKE) clean

tags:
	coqtags `find . -name \*.v`

doc:
	coqdoc --html -g -d doc -R . CoLoR `find . -name \*.v`
	./createIndex

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
