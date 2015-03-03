# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

LIBNAME := CoLoR

.SUFFIXES:

.PHONY: default config clean clean-all clean-doc tags doc install-doc install-dist

MAKECOQ := +$(MAKE) -r -f Makefile.coq

VFILES := $(shell find . -name \*.v | grep -v .\# | sed -e 's|^./||g')

default: Makefile.coq
	$(MAKECOQ)

config Makefile.coq:
	echo -R . $(LIBNAME) $(VFILES) > _CoqProject
	coq_makefile -f _CoqProject > Makefile.coq

clean:
	rm -f `find . -name \*~`
	$(MAKECOQ) clean

clean-all: clean
	rm -f Makefile.coq _CoqProject

clean-doc:
	rm -f doc/$(LIBNAME).*.html doc/index.html doc/main.html

tags:
	coqtags $(VFILES)

doc:
	coqdoc --html -g -d doc -R . $(LIBNAME) `find . -path ./Coccinelle -prune -o -name \*.v -print`
	./create_index

WEB := ~/rewriting-svn/web/wdfs/color
#LOCAL := ~/rewriting-svn/web/color/site

install-doc:
	rm -f $(WEB)/doc/coqdoc.css $(WEB)/doc/*.html
	cp -f doc/coqdoc.css doc/*.html $(WEB)/doc
#	cp -f doc/coqdoc.css doc/*.html $(LOCAL)/doc

install-dist:
#	cp -f CoLoR_`date +%y%m%d`.tar.gz $(WEB)/CoLoR.tar.gz
	cp -f CHANGES $(WEB)/CHANGES.CoLoR
#	cp -f CHANGES $(LOCAL)/CHANGES.CoLoR

%.vo: %.v
	$(MAKECOQ) $@

%:
	$(MAKECOQ) $@
