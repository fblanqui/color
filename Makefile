# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

SHELL := /bin/sh

MAKEFLAGS := -r

.SUFFIXES:

.PHONY: clean clean-doc compile config default dist doc dump html install-dist install-doc tags

SUBDIRS := Util Term PolyInt DP Filter MPO Conversion RPO HORPO

DUMP := /tmp/dump
WEB := /local/color/htdocs

default:
	for d in $(SUBDIRS); do $(MAKE) -C $$d OTHERFLAGS="-dont-load-proofs"; done

clean:
	rm -f `find . -name \*~ -o -name .\*~`
	for d in $(SUBDIRS); do $(MAKE) -C $$d clean; done

clean-doc:
	rm -f $(DUMP) doc/Rewriting.*.html doc/index.html

tags:
	coqtags `find . -name \*.v`

dump: clean-doc clean
	$(MAKE) OTHERFLAGS="-dont-load-proofs -dump-glob $(DUMP)"

html:
	coqdoc --html -g -d doc --glob-from $(DUMP) -R `pwd` Rewriting `find . -name \*.v`
	./createIndex

doc: dump html

install-doc:
	rm -rf $(WEB)/doc
	mkdir $(WEB)/doc
	cp doc/*.html doc/style.css $(WEB)/doc

dist:
	./createDist

install-dist:
	cp CoLoR_`date +%y%m%d`.tar.gz $(WEB)/CoLoR/
	mv -f CoLoR_`date +%y%m%d`.tar.gz $(WEB)/CoLoR.tar.gz
	cp -f CHANGES $(WEB)/CHANGES.CoLoR

config:
	./createMakefiles
	$(MAKE) depend

compile: config
	$(MAKE)

%:
	for d in $(SUBDIRS); do $(MAKE) -C $$d $*; done
