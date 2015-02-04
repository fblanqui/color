# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2015-02-04

LIBNAME := Coccinelle_for_CoLoR

.SUFFIXES:

.PHONY: default config clean clean-all clean-doc tags install doc

MAKECOQ := $(MAKE) -r -f Makefile.coq

VFILES := $(shell find . -name \*.v | grep -v .\#)

default: Makefile.coq
	+$(MAKECOQ)

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

INSTALL_DIR ?= `coqtop -where`/user-contrib

install:
	+for i in `find . -name \*.vo`; do \
	  install -d $(INSTALL_DIR)/$(LIBNAME)/$$i; \
	  install -m 0644 $$i $(INSTALL_DIR)/$(LIBNAME)/$$i; \
	done

doc:
	coqdoc --html -g -d doc -R . $(LIBNAME) `find . -name \*.v -print`
	./createIndex

%.vo: %.v
	$(MAKECOQ) $@

%:
	$(MAKECOQ) $@
