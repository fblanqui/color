# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

SHELL := /bin/sh

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean all config dist doc install-dist install-doc tags

COQMAKE := $(MAKE) -f Makefile.coq

all: Makefile.coq
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

WEB := /local/web-serveurs/color/htdocs
ADR := blanqui@loria.loria.fr

install-doc:
	ssh $(ADR) "rm -rf $(WEB)/doc; mkdir $(WEB)/doc"
	scp doc/*.html doc/coqdoc.css $(ADR):$(WEB)/doc
	scp CHANGES $(ADR):$(WEB)/CHANGES.CoLoR

dist:
	./createDist

install-dist:
	mv -f CoLoR_`date +%y%m%d`.tar.gz $(WEB)/CoLoR.tar.gz
	cp -f CHANGES $(WEB)/CHANGES.CoLoR

%.vo: %.v
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs" $@

%:
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs" $@
