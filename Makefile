# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

SHELL := /bin/sh

MAKEFLAGS := -r

.SUFFIXES:

.PHONY: clean all makefiles dist doc dump html install-dist install-doc tags

SUBDIRS := Util Term MannaNess PolyInt DP Filter MPO Conversion RPO HORPO

DUMP := /tmp/dump
WEB := /local/color/htdocs

all: Util/Makefile
	for d in $(SUBDIRS); do $(MAKE) -C $$d OTHERFLAGS="-dont-load-proofs"; done

Util/Makefile:
	$(MAKE) makefiles

clean:
	rm -f *~ .*~ $(DUMP) doc/Rewriting.*.html doc/index.html
	for d in $(SUBDIRS); do $(MAKE) -C $$d clean; done

tags:
	coqtags `find . -name \*.v`

dump:
	for d in $(SUBDIRS); do $(MAKE) -C $$d OTHERFLAGS="-dont-load-proofs -dump-glob $(DUMP)"; done

html:
	coqdoc --html -g -d doc --glob-from $(DUMP) -R `pwd` Rewriting `find . -name \*.v`
	./createIndex

doc: clean dump html

install-doc:
	rm -rf $(WEB)/doc
	mkdir $(WEB)/doc
	cp doc/*.html doc/coqdoc.css $(WEB)/doc
	cp -f CHANGES $(WEB)/CHANGES.CoLoR

dist:
	./createDist

install-dist:
	cp CoLoR_`date +%y%m%d`.tar.gz $(WEB)/CoLoR/
	mv -f CoLoR_`date +%y%m%d`.tar.gz $(WEB)/CoLoR.tar.gz
	cp -f CHANGES $(WEB)/CHANGES.CoLoR

makefiles:
	./createMakefiles
	$(MAKE) depend

%:
	for d in $(SUBDIRS); do $(MAKE) -C $$d $*; done
