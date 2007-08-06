# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

SHELL := /bin/sh

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean all config dist doc dump html install-dist install-doc tags

DUMP := /tmp/dump
WEB := /local/color/htdocs

COQMAKE := $(MAKE) -f Makefile.coq

all: Makefile.coq
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs"

Makefile.coq:
	$(MAKE) config

config:
	coq_makefile -R . Rewriting `find . -name \*.v` > Makefile.coq
	$(COQMAKE) depend

clean:
	rm -f `find . -name \*~`
	rm -f $(DUMP) doc/Rewriting.*.html doc/index.html
	$(COQMAKE) clean

tags:
	coqtags `find . -name \*.v`

$(DUMP): dump

dump: clean
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs -dump-glob $(DUMP)"

html: $(DUMP)
	coqdoc --html -g -d doc --glob-from $(DUMP) -R . Rewriting `find . -name \*.v`
	./createIndex

doc: dump html

install-doc:
	rm -rf $(WEB)/doc
	mkdir $(WEB)/doc
	cp doc/*.html doc/coqdoc.css $(WEB)/doc
	cp -f CHANGES $(WEB)/CHANGES.CoLoR

dist:
	./createDist

install-dist:
	mv -f CoLoR_`date +%y%m%d`.tar.gz $(WEB)/CoLoR.tar.gz
	cp -f CHANGES $(WEB)/CHANGES.CoLoR

%:
	$(COQMAKE) OTHERFLAGS="-dont-load-proofs" $*
