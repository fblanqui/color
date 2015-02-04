# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

LIBNAME := CoLoR

.SUFFIXES:

.PHONY: default config clean clean-all clean-doc tags doc dist install-doc install-dist

MAKECOQ := +$(MAKE) -r -f Makefile.coq

VFILES := $(shell find . -name \*.v | grep -v .\#)

default: Makefile.coq
	$(MAKECOQ)

config Makefile.coq:
	coq_makefile -R . $(LIBNAME) $(VFILES) > Makefile.coq
	$(MAKECOQ) depend

clean:
	rm -f `find . -name \*~`
	$(MAKECOQ) clean

clean-all: clean
	rm -f Makefile.coq

clean-doc:
	rm -f doc/$(LIBNAME).*.html doc/index.html doc/main.html

tags:
	coqtags `find . -name \*.v`

doc:
	coqdoc --html -g -d doc -R . $(LIBNAME) `find . -path ./Coccinelle -prune -o -name \*.v -print`
	./createIndex

dist:
	./createDist

ADR := ~/rewriting-svn/web/wdfs/color
#LOCAL := ~/rewriting-svn/web/color/site

install-doc:
	rm -f $(ADR)/doc/coqdoc.css $(ADR)/doc/*.html
	cp doc/coqdoc.css doc/*.html $(ADR)/doc
#	cp doc/coqdoc.css doc/*.html $(LOCAL)/doc

install-dist:
	cp CoLoR_`date +%y%m%d`.tar.gz $(ADR)/CoLoR.tar.gz
	cp CHANGES $(ADR)/CHANGES.CoLoR
#	cp CHANGES $(LOCAL)/CHANGES.CoLoR

%.vo: %.v
	$(MAKECOQ) $@

%:
	$(MAKECOQ) $@
